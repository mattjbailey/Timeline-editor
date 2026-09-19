#!/usr/bin/env python3
"""
Lighting Designer - PyQt6 Prototype
A modern, touch-friendly DMX fixture management and effect creation tool.
"""

import sys
import os

# Ensure the project root is on sys.path so 'shared' package is importable
_project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _project_root not in sys.path:
    sys.path.insert(0, _project_root)

# ── OpenCV FFmpeg DLL crash workaround ────────────────────────────
# opencv_videoio_ffmpeg4130_64.dll crashes intermittently with
# 0xC0000005 (ACCESS_VIOLATION) regardless of console mode.
# Disable OpenCV's FFmpeg backend entirely; video decoding now uses
# ffmpeg subprocess via FFmpegVideoReader (lighting_designer/ffmpeg_reader.py).
os.environ['OPENCV_VIDEOIO_PRIORITY_FFMPEG'] = '0'
os.environ['OPENCV_FFMPEG_LOGLEVEL'] = '-8'

import tempfile
import traceback
import threading
from datetime import datetime
from PyQt6.QtWidgets import QApplication, QMessageBox
from PyQt6.QtNetwork import QLocalServer, QLocalSocket
from gui import LightingDesignerWindow

# Single instance lock name
LOCK_NAME = "LightingDesigner_SingleInstance_Lock"

# Crash log path — persists across launches (append mode)
_CRASH_LOG = os.path.join(os.path.expanduser('~'), 'lighting_designer_crash.log')

# Appertini client — initialised in main(), used by crash handlers
_appertini_client = None

_LD_API_KEY = "aptr_X88aUdghbnntncSsEYptZaSuYgdpVvwX5V5F7eyBRjY"


class _AppWithErrorReporting(QApplication):
    """QApplication subclass that catches exceptions raised inside Qt event
    handlers / slots and forwards them to Appertini.  Without this override,
    PyQt6 can swallow such exceptions or surface them as the opaque
    'SystemError: returned a result with an exception set'."""

    def notify(self, receiver, event):
        import time as _time
        _t0 = _time.perf_counter()
        try:
            result = super().notify(receiver, event)
            _elapsed = (_time.perf_counter() - _t0) * 1000.0
            if _elapsed > 200:
                import logging as _nl
                _nl.getLogger('lighting_designer').warning(
                    f"[notify] SLOW event {event.type()} on {type(receiver).__name__}: "
                    f"{_elapsed:.0f}ms")
            return result
        except Exception as exc:
            import traceback as _ntb
            # Report to Appertini only — do NOT log to stderr/logging because
            # --noconsole builds route that output to a Windows popup dialog.
            _report_to_appertini(
                type(exc), exc, exc.__traceback__,
                action="qt_event_exception",
            )
            return False


def _report_to_appertini(exc_type, exc_value, exc_tb, *, action="uncaught_exception",
                         thread_name=None, _blocking=False):
    """Send an error report to Appertini on a background thread.

    Set *_blocking=True* when called from a crash handler right before the
    process exits — the thread is joined (up to 8 s) so the HTTP POST has
    time to complete before Python tears down daemon threads.
    """
    if _appertini_client is None:
        return None
    try:
        tb_text = ''.join(traceback.format_exception(exc_type, exc_value, exc_tb))
    except Exception:
        tb_text = ""
    ctx = {
        "action": action,
        "error_type": getattr(exc_type, '__name__', str(exc_type)),
        "error_message": str(exc_value),
        "traceback": tb_text,
    }
    if thread_name:
        ctx["thread_name"] = thread_name

    def _send():
        try:
            _appertini_client.report_error(
                exc_value,
                severity="high",
                extra_context=ctx,
            )
        except Exception:
            pass

    try:
        # Use daemon=False only when the caller will join() it; otherwise keep
        # it as a daemon so it doesn't prevent a clean exit in normal operation.
        t = threading.Thread(target=_send, name="appertini-report", daemon=not _blocking)
        t.start()
        return t
    except Exception:
        return None


def _write_crash(exc_type, exc_value, exc_tb):
    """Global exception handler that writes unhandled exceptions to a crash log."""
    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    tb_text = ''.join(traceback.format_exception(exc_type, exc_value, exc_tb))
    entry = f"\n{'='*60}\n[CRASH] {timestamp}\n{'='*60}\n{tb_text}\n"
    try:
        with open(_CRASH_LOG, 'a', encoding='utf-8') as f:
            f.write(entry)
            f.flush()
    except Exception:
        pass  # Last resort — can't write the crash log
    # Report to Appertini — use blocking mode so the HTTP POST completes
    # before sys.__excepthook__ exits the process (which would kill daemon threads).
    t = _report_to_appertini(exc_type, exc_value, exc_tb, _blocking=True)
    if t is not None:
        try:
            t.join(timeout=8.0)
        except Exception:
            pass
    # Also print to stderr so it's visible in the console
    sys.__excepthook__(exc_type, exc_value, exc_tb)


def _thread_exception_handler(args):
    """Catch exceptions in background threads and report to Appertini."""
    _report_to_appertini(
        args.exc_type, args.exc_value, args.exc_traceback,
        action="thread_exception",
        thread_name=args.thread.name if args.thread else "unknown",
    )


def _kill_stale_instances():
    """Kill any orphaned pythonw processes running this same main.py.
    
    After a crash the process may linger as a zombie holding the named-pipe
    lock.  We detect siblings by matching the command-line to our own script
    path and kill them (skipping ourselves).
    """
    try:
        import psutil
    except ImportError:
        # psutil not available – fall back to a simpler approach
        return

    my_pid = os.getpid()
    # Normalise our own script path for comparison
    my_script = os.path.normcase(os.path.abspath(__file__))
    killed = []

    for proc in psutil.process_iter(['pid', 'name', 'cmdline']):
        try:
            if proc.pid == my_pid:
                continue
            name = (proc.info.get('name') or '').lower()
            if 'python' not in name:
                continue
            cmdline = proc.info.get('cmdline') or []
            # Check if any arg matches our script path
            for arg in cmdline:
                if os.path.normcase(os.path.abspath(arg)) == my_script:
                    proc.kill()
                    killed.append(proc.pid)
                    break
        except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
            pass

    if killed:
        print(f"Killed {len(killed)} stale instance(s): {killed}")
        # Give OS a moment to release the named-pipe
        import time
        time.sleep(0.3)


def check_single_instance():
    """Check if another instance is already running.
    
    Returns:
        tuple: (is_single, socket/server) - socket if another instance exists, server if we're first
    """
    # 1) Try to connect to an already-running instance
    socket = QLocalSocket()
    socket.connectToServer(LOCK_NAME)
    
    if socket.waitForConnected(300):
        # Something answered — but it might be a zombie.  Kill stale
        # instances and try again.
        socket.close()
        _kill_stale_instances()

        # Remove stale pipe and retry
        QLocalServer.removeServer(LOCK_NAME)
        socket2 = QLocalSocket()
        socket2.connectToServer(LOCK_NAME)
        if socket2.waitForConnected(300):
            # Still alive after cleanup — genuinely running
            socket2.close()
            return False, None
        socket2.close()
    
    # 2) No live instance — remove any stale socket left by a crash
    QLocalServer.removeServer(LOCK_NAME)
    
    # 3) Create our own server to hold the lock
    server = QLocalServer()
    
    if not server.listen(LOCK_NAME):
        # Failed to create server - might be permission issue; continue anyway
        print(f"Warning: Could not create single-instance lock: {server.errorString()}")
        return True, None
    
    return True, server


def _unraisable_exception_handler(unraisable):
    """Catch exceptions that Python cannot raise normally.

    These include exceptions inside cffi/ctypes callbacks (e.g. the
    ``sounddevice`` PortAudio callback after a sleep/wake cycle), exceptions
    in ``__del__`` finalizers, and weak-reference callbacks.  Python prints
    them as "Exception ignored in: ..." on stderr and calls this hook.

    We forward them to Appertini as low-severity informational reports so
    we can track real-world occurrences without cluttering the crash log.
    """
    try:
        exc_type = unraisable.exc_type
        exc_value = unraisable.exc_value
        exc_tb = getattr(unraisable, 'exc_traceback', None)
        obj = getattr(unraisable, 'object', None)
        obj_str = repr(obj) if obj is not None else "<unknown>"
        # Write to crash log only — do NOT print to stderr, because
        # --noconsole PyInstaller builds route stderr to a Windows
        # message dialog which causes intrusive popups for harmless errors.
        # Write to crash log with reduced emphasis
        try:
            tb_text = ''.join(traceback.format_exception(exc_type, exc_value, exc_tb))
        except Exception:
            tb_text = str(exc_value)
        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        entry = (f"\n{'─'*60}\n[UNRAISABLE] {timestamp}  object={obj_str}\n"
                 f"{tb_text}\n")
        try:
            with open(_CRASH_LOG, 'a', encoding='utf-8') as f:
                f.write(entry)
        except Exception:
            pass
        # Forward to Appertini so real-world occurrences (e.g. the empty
        # "Python-CFFI error" from the sounddevice/PortAudio callback after a
        # sleep/wake cycle) are tracked.  Reported at low severity and on a
        # daemon thread so it never blocks or crashes the app.
        try:
            _report_to_appertini(
                exc_type, exc_value, exc_tb,
                action="unraisable_exception",
            )
        except Exception:
            pass
    except Exception:
        pass  # absolutely last resort


class _CrashLogStream:
    """Minimal write-only stream that appends to the crash log.

    Used to replace sys.stderr / sys.stdout when they are None (windowed
    PyInstaller builds).  Guarantees a valid file-like object so that cffi /
    PortAudio traceback prints are captured to the log instead of triggering
    the empty "Python-CFFI error" dialog on Windows.
    """

    def write(self, text):
        try:
            if text and text.strip():
                with open(_CRASH_LOG, 'a', encoding='utf-8') as f:
                    f.write(text)
        except Exception:
            pass
        return len(text) if text else 0

    def flush(self):
        pass

    def isatty(self):
        return False


def _install_stream_guard():
    """Ensure sys.stderr and sys.stdout are never None."""
    try:
        if sys.stderr is None:
            sys.stderr = _CrashLogStream()
        if sys.stdout is None:
            sys.stdout = _CrashLogStream()
    except Exception:
        pass


# Strong reference to the redirected log file — keeps its fd open for the
# lifetime of the process so the OS std handles stay valid.
_native_log_file = None


def _redirect_native_stderr():
    """Point the process's OS-level stdout/stderr at the crash log.

    In --noconsole (pythonw / PyInstaller windowed) builds there is no console,
    so the C-runtime std handles are invalid.  When cffi's PortAudio callback
    raises and cffi tries to print the traceback, its native Windows fallback
    pops a blank ``Python-CFFI error`` MessageBox instead of writing to stderr —
    this path bypasses ``sys.stderr`` and every Python hook.  Redirecting the
    file descriptors *and* the Win32 STD_*_HANDLE to a real file makes cffi
    write the traceback to the crash log (no dialog); the log forwarder then
    ships it to Appertini.
    """
    global _native_log_file
    try:
        f = open(_CRASH_LOG, 'a', buffering=1, encoding='utf-8', errors='replace')
    except Exception:
        return
    _native_log_file = f  # keep alive for the whole process
    try:
        fd = f.fileno()
        # Redirect CRT file descriptors (covers native fprintf/stderr writes).
        try:
            os.dup2(fd, 1)
            os.dup2(fd, 2)
        except Exception:
            pass
        # Redirect the Win32 standard handles (covers cffi's GetStdHandle path,
        # which is what pops the blank "Python-CFFI error" dialog).
        if sys.platform == 'win32':
            try:
                import msvcrt
                import ctypes
                handle = msvcrt.get_osfhandle(fd)
                STD_OUTPUT_HANDLE = -11
                STD_ERROR_HANDLE = -12
                _k32 = ctypes.windll.kernel32
                _k32.SetStdHandle(STD_OUTPUT_HANDLE, ctypes.c_void_p(handle))
                _k32.SetStdHandle(STD_ERROR_HANDLE, ctypes.c_void_p(handle))
            except Exception:
                pass
        # Point Python's own streams at the same file so logging/prints land in
        # the crash log too (they are None in windowed builds).
        try:
            sys.stderr = f
            sys.stdout = f
        except Exception:
            pass
    except Exception:
        pass


def _report_text_to_appertini(title, text, *, action="native_error"):
    """Forward a raw error/traceback string to Appertini.

    Used for native cffi / PortAudio output that has no Python exception object
    (it is printed by cffi's C code and captured from the crash log).  A
    synthetic exception carries the text through the existing report API.
    """
    if _appertini_client is None:
        return
    ctx = {
        "action": action,
        "error_type": "CFFICallbackError",
        "error_message": title,
        "traceback": text[:8000],
    }

    def _send():
        try:
            _appertini_client.report_error(
                RuntimeError(f"{title}: {text[:300]}"),
                severity="high",
                extra_context=ctx,
            )
        except Exception:
            pass

    try:
        threading.Thread(target=_send, name="appertini-cffi-report",
                         daemon=True).start()
    except Exception:
        pass


_cffi_forwarder_started = False


def _start_cffi_log_forwarder():
    """Tail the crash log and forward native cffi / PortAudio callback errors
    to Appertini.

    These originate in cffi's C-level traceback printer (redirected to the
    crash log by :func:`_redirect_native_stderr`) and therefore bypass Python's
    exception hooks, so they would otherwise never reach Appertini.  We tail the
    file, match cffi/PortAudio signatures, and forward de-duplicated blocks.
    """
    global _cffi_forwarder_started
    if _cffi_forwarder_started:
        return
    _cffi_forwarder_started = True

    import hashlib
    import time as _t

    markers = ("from cffi callback", "portaudioerror", "_cffi_backend",
               "cffi", "pa_", "sounddevice")

    def _tail():
        try:
            pos = os.path.getsize(_CRASH_LOG)
        except Exception:
            pos = 0
        seen = set()
        while True:
            try:
                _t.sleep(3.0)
                try:
                    size = os.path.getsize(_CRASH_LOG)
                except Exception:
                    continue
                if size < pos:
                    pos = 0  # log truncated / rotated
                if size == pos:
                    continue
                with open(_CRASH_LOG, 'r', encoding='utf-8', errors='replace') as fh:
                    fh.seek(pos)
                    chunk = fh.read()
                    pos = fh.tell()
                if not chunk:
                    continue
                low = chunk.lower()
                if not any(m in low for m in markers):
                    continue
                digest = hashlib.md5(chunk.encode('utf-8', 'replace')).hexdigest()
                if digest in seen:
                    continue
                seen.add(digest)
                _report_text_to_appertini(
                    "Native cffi/PortAudio callback error",
                    chunk.strip(),
                    action="cffi_native_error",
                )
            except Exception:
                pass

    try:
        threading.Thread(target=_tail, name="cffi-log-forwarder",
                         daemon=True).start()
    except Exception:
        pass


def main():
    # Install crash handler BEFORE anything else
    sys.excepthook = _write_crash
    threading.excepthook = _thread_exception_handler
    sys.unraisablehook = _unraisable_exception_handler

    # Guard sys.stderr / sys.stdout so they are never None.  In --noconsole
    # PyInstaller (runw.exe) builds there is no console, so sys.stderr is None.
    # When cffi's callback error printer or PortAudio writes a traceback to
    # stderr, the write on a None/invalid handle surfaces as the opaque,
    # empty "Python-CFFI error" MessageBox.
    #
    # _redirect_native_stderr() is the primary defence: it redirects the OS
    # file descriptors AND the Win32 STD_*_HANDLE to the crash log so cffi's
    # C-level fallback writes the traceback to the log instead of popping the
    # dialog.  _install_stream_guard() remains as a Python-level safety net in
    # case the OS-level redirect fails.
    _redirect_native_stderr()
    _install_stream_guard()

    # Enable faulthandler so that native/C-level crashes (ACCESS_VIOLATION,
    # PortAudio abort, DLL crash) write a Python stack trace to the crash log
    # file instead of silently disappearing.  This is a best-effort dump;
    # faulthandler writes synchronously from a signal handler so it completes
    # even when the normal Python exception hooks don't run.
    try:
        import faulthandler
        _fh_file = open(_CRASH_LOG, 'a', encoding='utf-8')
        from datetime import datetime as _dt
        _fh_file.write(f"\n{'='*60}\n[SESSION START] {_dt.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        _fh_file.flush()
        faulthandler.enable(file=_fh_file, all_threads=True)
    except Exception:
        pass

    # Initialise Appertini error reporting (best-effort).
    # SDK >= 1.0.7 exposes install_crash_handler() which covers sys.excepthook
    # and threading.excepthook.  We always keep our own faulthandler setup
    # (native/segfault crashes) and sys.unraisablehook (exceptions in __del__
    # etc.) on top, since the SDK does NOT cover those.
    global _appertini_client
    try:
        from appertini import AppertiniClient
        _appertini_client = AppertiniClient(_LD_API_KEY)
        # SDK >= 1.0.7: call install_crash_handler() for standard Python/thread
        # coverage.  Our faulthandler + unraisablehook are layered on top and
        # kept unconditionally — they chain cleanly because the SDK's handlers
        # call through to the previous hook.
        if callable(getattr(_appertini_client, 'install_crash_handler', None)):
            _appertini_client.install_crash_handler()
            # Re-apply our unraisablehook after the SDK may have replaced it.
            sys.unraisablehook = _unraisable_exception_handler
        try:
            _appertini_client.get_app_info()
        except Exception:
            pass  # network error is fine
    except ImportError:
        _appertini_client = None
    except Exception:
        _appertini_client = None

    # Start the background forwarder that ships native cffi / PortAudio
    # callback errors (captured in the crash log) to Appertini.  These bypass
    # Python's exception hooks, so this tailer is the only path that reports
    # them for diagnosis.
    _start_cffi_log_forwarder()

    # Wire the visualizer engine's error hook so audio/stream errors it catches
    # (e.g. "audio_stream_open_retry" after stale-PortAudio recovery) are
    # forwarded to Appertini.  Without this the hook stays None and those
    # errors only land in ~/viz_debug.log.
    def _viz_error_reporter(exc_type, exc_value, exc_tb, *, context="visualizer"):
        _report_to_appertini(exc_type, exc_value, exc_tb, action=f"viz_{context}")

    try:
        try:
            import visualizer_engine as _viz_mod
        except ImportError:
            from lighting_designer import visualizer_engine as _viz_mod
        _viz_mod._error_reporter = _viz_error_reporter
    except Exception:
        pass

    # Record session start time for usage logging
    import time as _time
    _session_start = _time.time()

    # Snapshot license info on a background thread so startup isn't delayed.
    # Stored in a mutable container so the exit handler can read it later.
    _license_info: dict = {"status": "unknown", "tier": None, "key_last4": None}

    def _fetch_license_info():
        try:
            if _appertini_client is None:
                return
            status = _appertini_client.check_license()
            _license_info["status"] = status.status or "unknown"
            _license_info["tier"] = status.tier_name
            cached_key = _appertini_client._load_cached_key()
            if cached_key:
                _license_info["key_last4"] = f"****-{cached_key[-4:]}"
        except Exception:
            pass

    threading.Thread(target=_fetch_license_info, name="appertini-license-check",
                     daemon=True).start()

    app = _AppWithErrorReporting(sys.argv)
    app.setApplicationName("Lighting Designer")
    app.setOrganizationName("TimelineEditor")

    # Check for single instance
    is_single, lock = check_single_instance()

    if not is_single:
        QMessageBox.warning(
            None,
            "Already Running",
            "Another instance of Lighting Designer is already running.\n\n"
            "Please close the other instance before starting a new one.\n\n"
            "Only one instance can run at a time to prevent conflicts with Art-Net output."
        )
        sys.exit(1)

    window = LightingDesignerWindow()
    window._appertini_client = _appertini_client
    window.show()

    result = app.exec()

    # --- Session-end usage log ---
    # Send an informational log to Appertini with license identity + duration.
    # Runs synchronously (with a short timeout) so it completes before exit.
    try:
        if _appertini_client is not None:
            _elapsed_sec = _time.time() - _session_start
            _hours, _rem = divmod(int(_elapsed_sec), 3600)
            _mins, _secs = divmod(_rem, 60)
            _duration_str = (f"{_hours}h {_mins}m {_secs}s" if _hours
                             else f"{_mins}m {_secs}s")
            _key_str = _license_info.get("key_last4") or "no key"
            _tier_str = _license_info.get("tier") or _license_info.get("status", "unknown")
            _msg = (f"Session ended — license: {_key_str} ({_tier_str}) — "
                    f"duration: {_duration_str}")
            _meta = {
                "license_status": _license_info.get("status"),
                "license_tier": _license_info.get("tier"),
                "license_key_last4": _license_info.get("key_last4"),
                "session_duration_seconds": round(_elapsed_sec),
                "session_duration_human": _duration_str,
            }

            def _send_session_log():
                try:
                    _appertini_client.log(
                        _msg,
                        level="INFO",
                        logger_name="session",
                        metadata=_meta,
                    )
                except Exception:
                    pass

            t = threading.Thread(target=_send_session_log,
                                 name="appertini-session-log", daemon=False)
            t.start()
            t.join(timeout=6.0)
    except Exception:
        pass

    # Clean up lock
    if lock:
        lock.close()

    sys.exit(result)


if __name__ == "__main__":
    main()
