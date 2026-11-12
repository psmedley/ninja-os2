// Copyright 2012 Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "exit_status.h"
#include "subprocess.h"

#include <sys/select.h>
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <spawn.h>
#include <sys/time.h>
#ifdef __OS2__
#include <signal.h>
#include <stdlib.h>  // _beginthread
#include <sys/socket.h>
#endif

#ifdef __OS2__
#define BIN_SH "/@unixroot/usr/bin/sh"
#else
#define BIN_SH "/bin/sh"
#endif

#if defined(USE_PPOLL)
#include <poll.h>
#else
#include <sys/select.h>
#endif

extern char** environ;

#include "util.h"

using namespace std;

namespace {
  ExitStatus ParseExitStatus(int status);

#ifdef __OS2__
// Copies a job's output from the pipe it writes to into the socket ninja
// select()s on (see Subprocess::Start()), then closes both ends, so that ninja
// sees EOF on the socket once the job (and anything that inherited its stdout)
// is done.
void OutputPumpThread(void* arg) {
  int* fds = static_cast<int*>(arg);
  int in = fds[0];
  int out = fds[1];
  delete[] fds;

  // Don't let a write after ninja stopped reading (e.g. after Ctrl-C) kill
  // ninja with SIGPIPE; ninja's other signals stay blocked in this thread.
  sigset_t set;
  sigemptyset(&set);
  sigaddset(&set, SIGPIPE);
  sigaddset(&set, SIGINT);
  sigaddset(&set, SIGTERM);
  sigaddset(&set, SIGHUP);
  sigaddset(&set, SIGCHLD);
  sigprocmask(SIG_BLOCK, &set, NULL);

  char buf[4 << 10];
  bool discard = false;
  for (;;) {
    ssize_t len = read(in, buf, sizeof(buf));
    if (len < 0 && errno == EINTR)
      continue;
    if (len <= 0)
      break;
    const char* p = buf;
    while (len > 0 && !discard) {
      ssize_t written = write(out, p, len);
      if (written < 0) {
        if (errno == EINTR)
          continue;
        // ninja stopped reading (e.g. it is shutting down). Keep draining the
        // pipe so the job doesn't block on a full pipe, but drop the output.
        discard = true;
        break;
      }
      p += written;
      len -= written;
    }
  }
  close(in);
  close(out);
}
#endif
}

Subprocess::Subprocess(bool use_console) : fd_(-1), pid_(-1),
                                           use_console_(use_console) {
}

Subprocess::~Subprocess() {
  if (fd_ >= 0)
    close(fd_);
  // Reap child if forgotten.
  if (pid_ != -1)
    Finish();
}

bool Subprocess::Start(SubprocessSet* set, const string& command) {
  int subproc_stdout_fd = -1;
#ifdef __OS2__
  int* pump_fds = NULL;
#endif
  if (use_console_) {
    fd_ = -1;
  } else {
    int output_pipe[2];
#ifdef __OS2__
    // select() only works with sockets on OS/2 (LIBCx doesn't support native
    // pipes yet, https://github.com/bitwiseworks/libcx/issues/34), so ninja
    // waits on a socketpair. However, the job must not get the socket as its
    // stdout/stderr: LIBCx's spawn2() (used e.g. by Python's subprocess) then
    // dup()s a socket for every process the job starts, which intermittently
    // fails with EBUSY, and non-kLIBC programs can't write to it at all.
    // Instead give the job a real pipe and let a thread pump the pipe into
    // the socketpair.
    int job_pipe[2];
    if (pipe(job_pipe) < 0)
      Fatal("pipe: %s", strerror(errno));
    if (socketpair(AF_LOCAL, SOCK_STREAM, 0, output_pipe) < 0)
      Fatal("socketpair: %s", strerror(errno));
    // Neither end the pump thread keeps may leak into other jobs, or ninja
    // would not see EOF until those jobs exit too.
    SetCloseOnExec(job_pipe[0]);
    SetCloseOnExec(output_pipe[1]);
    fd_ = output_pipe[0];
    subproc_stdout_fd = job_pipe[1];
    pump_fds = new int[2];
    pump_fds[0] = job_pipe[0];
    pump_fds[1] = output_pipe[1];
#else
    if (pipe(output_pipe) < 0)
      Fatal("pipe: %s", strerror(errno));
    fd_ = output_pipe[0];
    subproc_stdout_fd = output_pipe[1];
#endif
#if !defined(USE_PPOLL)
    // If available, we use ppoll in DoWork(); otherwise we use pselect
    // and so must avoid overly-large FDs.
    if (fd_ >= static_cast<int>(FD_SETSIZE))
      Fatal("pipe: %s", strerror(EMFILE));
#endif  // !USE_PPOLL
    SetCloseOnExec(fd_);
  }

  posix_spawn_file_actions_t action;
  int err = posix_spawn_file_actions_init(&action);
  if (err != 0)
    Fatal("posix_spawn_file_actions_init: %s", strerror(err));

  if (!use_console_) {
    err = posix_spawn_file_actions_addclose(&action, fd_);
    if (err != 0)
      Fatal("posix_spawn_file_actions_addclose: %s", strerror(err));
  }

  posix_spawnattr_t attr;
  err = posix_spawnattr_init(&attr);
  if (err != 0)
    Fatal("posix_spawnattr_init: %s", strerror(err));

  short flags = 0;

  flags |= POSIX_SPAWN_SETSIGMASK;
  err = posix_spawnattr_setsigmask(&attr, &set->old_mask_);
  if (err != 0)
    Fatal("posix_spawnattr_setsigmask: %s", strerror(err));
  // Signals which are set to be caught in the calling process image are set to
  // default action in the new process image, so no explicit
  // POSIX_SPAWN_SETSIGDEF parameter is needed.

  if (!use_console_) {
    // Put the child in its own process group, so ctrl-c won't reach it.
    flags |= POSIX_SPAWN_SETPGROUP;
    // No need to posix_spawnattr_setpgroup(&attr, 0), it's the default.

    // Open /dev/null over stdin.
    err = posix_spawn_file_actions_addopen(&action, 0, "/dev/null", O_RDONLY,
          0);
    if (err != 0) {
      Fatal("posix_spawn_file_actions_addopen: %s", strerror(err));
    }

    err = posix_spawn_file_actions_adddup2(&action, subproc_stdout_fd, 1);
    if (err != 0)
      Fatal("posix_spawn_file_actions_adddup2: %s", strerror(err));
    err = posix_spawn_file_actions_adddup2(&action, subproc_stdout_fd, 2);
    if (err != 0)
      Fatal("posix_spawn_file_actions_adddup2: %s", strerror(err));
    err = posix_spawn_file_actions_addclose(&action, subproc_stdout_fd);
    if (err != 0)
      Fatal("posix_spawn_file_actions_addclose: %s", strerror(err));
  }

#ifdef POSIX_SPAWN_USEVFORK
  flags |= POSIX_SPAWN_USEVFORK;
#endif

  err = posix_spawnattr_setflags(&attr, flags);
  if (err != 0)
    Fatal("posix_spawnattr_setflags: %s", strerror(err));

  const char* spawned_args[] = { BIN_SH, "-c", command.c_str(), NULL };
  err = posix_spawn(&pid_, BIN_SH, &action, &attr,
        const_cast<char**>(spawned_args), environ);
  if (err != 0)
    Fatal("posix_spawn: %s", strerror(err));

  err = posix_spawnattr_destroy(&attr);
  if (err != 0)
    Fatal("posix_spawnattr_destroy: %s", strerror(err));
  err = posix_spawn_file_actions_destroy(&action);
  if (err != 0)
    Fatal("posix_spawn_file_actions_destroy: %s", strerror(err));

  if (!use_console_)
    close(subproc_stdout_fd);
#ifdef __OS2__
  if (pump_fds) {
    int pump_read = pump_fds[0];
    int pump_write = pump_fds[1];
    if (_beginthread(OutputPumpThread, NULL, 64 << 10, pump_fds) == -1) {
      delete[] pump_fds;
      close(pump_read);
      close(pump_write);
      Fatal("_beginthread: %s", strerror(errno));
    }
  }
#endif
  return true;
}

void Subprocess::OnPipeReady() {
  char buf[4 << 10];
  ssize_t len = read(fd_, buf, sizeof(buf));
  if (len > 0) {
    buf_.append(buf, len);
  } else {
    if (len < 0)
      Fatal("read: %s", strerror(errno));
    close(fd_);
    fd_ = -1;
  }
}


bool Subprocess::TryFinish(int waitpid_options) {
  assert(pid_ != -1);
  int status, ret;
  while ((ret = waitpid(pid_, &status, waitpid_options)) < 0) {
    if (errno != EINTR)
      Fatal("waitpid(%d): %s", pid_, strerror(errno));
  }
  if (ret == 0)
    return false; // Subprocess is alive (WNOHANG-only).
  pid_ = -1;
  exit_status_ = ParseExitStatus(status);
  return true; // Subprocess has terminated.
}

ExitStatus Subprocess::Finish() {
  if (pid_ != -1) {
    TryFinish(0);
    assert(pid_ == -1);
  }
  return exit_status_;
}

namespace {

ExitStatus ParseExitStatus(int status) {
#ifdef _AIX
  if (WIFEXITED(status) && WEXITSTATUS(status) & 0x80) {
    // Map the shell's exit code used for signal failure (128 + signal) to the
    // status code expected by AIX WIFSIGNALED and WTERMSIG macros which, unlike
    // other systems, uses a different bit layout.
    int signal = WEXITSTATUS(status) & 0x7f;
    status = (signal << 16) | signal;
  }
#endif

  if (WIFEXITED(status)) {
    // propagate the status transparently
    return static_cast<ExitStatus>(WEXITSTATUS(status));
  }
  if (WIFSIGNALED(status)) {
    if (WTERMSIG(status) == SIGINT || WTERMSIG(status) == SIGTERM
        || WTERMSIG(status) == SIGHUP)
      return ExitInterrupted;
  }
  // At this point, we exit with any other signal+128
  return static_cast<ExitStatus>(status + 128);
}

} // anonymous namespace

bool Subprocess::Done() const {
  // Console subprocesses share console with ninja, and we consider them done
  // when they exit.
  // For other processes, we consider them done when we have consumed all their
  // output and closed their associated pipe.
  return (use_console_ && pid_ == -1) || (!use_console_ && fd_ == -1);
}

const string& Subprocess::GetOutput() const {
  return buf_;
}

volatile sig_atomic_t SubprocessSet::interrupted_;
volatile sig_atomic_t SubprocessSet::s_sigchld_received;

void SubprocessSet::SetInterruptedFlag(int signum) {
  interrupted_ = signum;
}

void SubprocessSet::SigChldHandler(int signo, siginfo_t* info, void* context) {
  s_sigchld_received = 1;
}

void SubprocessSet::HandlePendingInterruption() {
  sigset_t pending;
  sigemptyset(&pending);
  if (sigpending(&pending) == -1) {
    perror("ninja: sigpending");
    return;
  }
  if (sigismember(&pending, SIGINT))
    interrupted_ = SIGINT;
  else if (sigismember(&pending, SIGTERM))
    interrupted_ = SIGTERM;
  else if (sigismember(&pending, SIGHUP))
    interrupted_ = SIGHUP;
}

SubprocessSet::SubprocessSet() {
  // Block all these signals.
  // Their handlers will only be enabled during ppoll/pselect().
  sigset_t set;
  sigemptyset(&set);
  sigaddset(&set, SIGINT);
  sigaddset(&set, SIGTERM);
  sigaddset(&set, SIGHUP);
  sigaddset(&set, SIGCHLD);
  if (sigprocmask(SIG_BLOCK, &set, &old_mask_) < 0)
    Fatal("sigprocmask: %s", strerror(errno));

  struct sigaction act;
  memset(&act, 0, sizeof(act));
  act.sa_handler = SetInterruptedFlag;
  if (sigaction(SIGINT, &act, &old_int_act_) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigaction(SIGTERM, &act, &old_term_act_) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigaction(SIGHUP, &act, &old_hup_act_) < 0)
    Fatal("sigaction: %s", strerror(errno));

  memset(&act, 0, sizeof(act));
  act.sa_flags = SA_SIGINFO | SA_NOCLDSTOP;
  act.sa_sigaction = SigChldHandler;
  if (sigaction(SIGCHLD, &act, &old_chld_act_) < 0)
    Fatal("sigaction: %s", strerror(errno));
}

// Reaps console processes that have exited and moves them from the running set
// to the finished set.
void SubprocessSet::CheckConsoleProcessTerminated() {
  if (!s_sigchld_received)
    return;
  for (auto i = running_.begin(); i != running_.end(); ) {
    if ((*i)->use_console_ && (*i)->TryFinish(WNOHANG)) {
      finished_.push(*i);
      i = running_.erase(i);
    } else {
      ++i;
    }
  }
}

SubprocessSet::~SubprocessSet() {
  Clear();

  if (sigaction(SIGINT, &old_int_act_, 0) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigaction(SIGTERM, &old_term_act_, 0) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigaction(SIGHUP, &old_hup_act_, 0) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigaction(SIGCHLD, &old_chld_act_, 0) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigprocmask(SIG_SETMASK, &old_mask_, 0) < 0)
    Fatal("sigprocmask: %s", strerror(errno));
}

Subprocess *SubprocessSet::Add(const string& command, bool use_console) {
  Subprocess *subprocess = new Subprocess(use_console);
  if (!subprocess->Start(this, command)) {
    delete subprocess;
    return 0;
  }
  running_.push_back(subprocess);
  return subprocess;
}

#ifdef USE_PPOLL
bool SubprocessSet::DoWork() {
  vector<pollfd> fds;
  nfds_t nfds = 0;

  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i) {
    int fd = (*i)->fd_;
    if (fd < 0)
      continue;
    pollfd pfd = { fd, POLLIN | POLLPRI, 0 };
    fds.push_back(pfd);
    ++nfds;
  }
  if (nfds == 0) {
    // Add a dummy entry to prevent using an empty pollfd vector.
    // ppoll() allows to do this by setting fd < 0.
    pollfd pfd = { -1, 0, 0 };
    fds.push_back(pfd);
    ++nfds;
  }

  interrupted_ = 0;
  s_sigchld_received = 0;
  int ret = ppoll(&fds.front(), nfds, NULL, &old_mask_);
  // Note: This can remove console processes from the running set, but that is
  // not a problem for the pollfd set, as console processes are not part of the
  // pollfd set (they don't have a fd).
  CheckConsoleProcessTerminated();
  if (ret == -1) {
    if (errno != EINTR) {
      perror("ninja: ppoll");
      return false;
    }
    return IsInterrupted();
  }

  // ppoll/pselect prioritizes file descriptor events over a signal delivery.
  // However, if the user is trying to quit ninja, we should react as fast as
  // possible.
  HandlePendingInterruption();
  if (IsInterrupted())
    return true;

  // Iterate through both the pollfd set and the running set.
  // All valid fds in the running set are in the pollfd, in the same order.
  nfds_t cur_nfd = 0;
  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ) {
    int fd = (*i)->fd_;
    if (fd < 0) {
      ++i;
      continue;
    }
    assert(fd == fds[cur_nfd].fd);
    if (fds[cur_nfd++].revents) {
      (*i)->OnPipeReady();
      if ((*i)->Done()) {
        finished_.push(*i);
        i = running_.erase(i);
        continue;
      }
    }
    ++i;
  }

  return IsInterrupted();
}

#else  // !defined(USE_PPOLL)
bool SubprocessSet::DoWork() {
  fd_set set;
  int nfds = 0;
  FD_ZERO(&set);

  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i) {
    int fd = (*i)->fd_;
    if (fd >= 0) {
      FD_SET(fd, &set);
      if (nfds < fd+1)
        nfds = fd+1;
    }
  }

  interrupted_ = 0;
  s_sigchld_received = 0;
#ifdef __OS2__
  // kLIBC has no pselect(), so emulate it non-atomically: unblock the signals
  // that are blocked in the constructor (SIGINT/SIGTERM/SIGHUP/SIGCHLD) for
  // the duration of select(), then block them again.
  //
  // Since ninja 1.12, console subprocesses have no pipe (fd_ == -1) and their
  // termination is only detected via SIGCHLD + waitpid(WNOHANG). With plain
  // select() and SIGCHLD blocked, a console job (e.g. a CMake USES_TERMINAL
  // step such as the nested Chromium build in qtwebengine) is never reaped and
  // ninja hangs forever once it is the last running job.
  //
  // Because unblock+select is not atomic, a signal arriving just before
  // select() could be missed, so use a short timeout while any console job is
  // running and poll those jobs with waitpid(WNOHANG) regardless of whether
  // SIGCHLD was seen.
  bool have_console = false;
  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i) {
    if ((*i)->use_console_) {
      have_console = true;
      break;
    }
  }
  struct timeval tv = { 0, 100 * 1000 };  // 100ms
  sigset_t blocked_mask;
  if (sigprocmask(SIG_SETMASK, &old_mask_, &blocked_mask) < 0)
    Fatal("sigprocmask: %s", strerror(errno));
  int ret = select(nfds, (nfds > 0 ? &set : nullptr), 0, 0,
                   have_console ? &tv : nullptr);
  int select_errno = errno;
  if (sigprocmask(SIG_SETMASK, &blocked_mask, 0) < 0)
    Fatal("sigprocmask: %s", strerror(errno));
  errno = select_errno;
  if (have_console)
    s_sigchld_received = 1;
#else
  int ret = pselect(nfds, (nfds > 0 ? &set : nullptr), 0, 0, 0, &old_mask_);
#endif
  CheckConsoleProcessTerminated();
  if (ret == -1) {
    if (errno != EINTR) {
      perror("ninja: pselect");
      return false;
    }
    return IsInterrupted();
  }

  // ppoll/pselect prioritizes file descriptor events over a signal delivery.
  // However, if the user is trying to quit ninja, we should react as fast as
  // possible.
  HandlePendingInterruption();
  if (IsInterrupted())
    return true;

  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ) {
    int fd = (*i)->fd_;
    if (fd >= 0 && FD_ISSET(fd, &set)) {
      (*i)->OnPipeReady();
      if ((*i)->Done()) {
        finished_.push(*i);
        i = running_.erase(i);
        continue;
      }
    }
    ++i;
  }

  return IsInterrupted();
}
#endif  // !defined(USE_PPOLL)

Subprocess* SubprocessSet::NextFinished() {
  if (finished_.empty())
    return NULL;
  Subprocess* subproc = finished_.front();
  finished_.pop();
  return subproc;
}

void SubprocessSet::Clear() {
  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i)
    // Since the foreground process is in our process group, it will receive
    // the interruption signal (i.e. SIGINT or SIGTERM) at the same time as us.
    if (!(*i)->use_console_)
      kill(-(*i)->pid_, interrupted_);
  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i)
    delete *i;
  running_.clear();
}
