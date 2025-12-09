import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import threading
import time
import socket
import base64
from datetime import timedelta
import wave
import struct
import os
import sys
import json
import webbrowser

# Initialize log file with clean ASCII header to avoid garbled remnants
try:
    with open("app_output.txt", "w", encoding="utf-8") as _lf:
        _lf.write("LOG START\n")
except Exception:
    pass

_VERBOSE_ENABLED = False
try:
    if sys.platform == "darwin":
        _VERBOSE_DIR = os.path.join(os.path.expanduser("~"), "Library", "Logs", "Timeline")
    elif os.name == "nt":
        _LOCALAPPDATA = os.environ.get("LOCALAPPDATA") or os.path.join(os.path.expanduser("~"), "AppData", "Local")
        _VERBOSE_DIR = os.path.join(_LOCALAPPDATA, "Timeline")
    else:
        _VERBOSE_DIR = os.path.join(os.path.expanduser("~"), ".local", "share", "Timeline")
    os.makedirs(_VERBOSE_DIR, exist_ok=True)
    _VERBOSE_FILE = os.path.join(_VERBOSE_DIR, "debug.txt")
except Exception:
    # Fallback to workspace root
    _VERBOSE_FILE = os.path.join(os.path.dirname(__file__), "..", "debug.txt")
_VERBOSE_MAX_BYTES = 5 * 1024 * 1024  # 5 MB simple rollover

def set_verbose_logging(enabled: bool):
    global _VERBOSE_ENABLED
    _VERBOSE_ENABLED = bool(enabled)

def debug_log(msg: str):
    try:
        print(msg)
    except Exception:
        pass
    try:
        # Write ASCII-only with Windows newlines to ensure universal readability
        s = str(msg)
        try:
            s_ascii = s.encode("ascii", errors="replace").decode("ascii")
        except Exception:
            s_ascii = s
        with open("app_output.txt", "a", encoding="ascii", errors="replace", newline="\r\n") as f:
            f.write(s_ascii + "\r\n")
            try:
                f.flush()
            except Exception:
                pass
        # When verbose logging is enabled, also write to debug.txt
        try:
            if _VERBOSE_ENABLED:
                # Simple size-based rollover
                try:
                    if os.path.exists(_VERBOSE_FILE) and os.path.getsize(_VERBOSE_FILE) > _VERBOSE_MAX_BYTES:
                        ts = time.strftime("%Y%m%d-%H%M%S")
                        rollover = _VERBOSE_FILE + "." + ts
                        try:
                            os.replace(_VERBOSE_FILE, rollover)
                        except Exception:
                            pass
                except Exception:
                    pass
                # Timestamped entry
                ts_line = time.strftime("%Y-%m-%d %H:%M:%S") + " - " + s
                with open(_VERBOSE_FILE, "a", encoding="utf-8", errors="replace") as df:
                    df.write(ts_line + "\n")
        except Exception:
            pass
    except Exception:
        pass

try:
    import mutagen
    import soundfile as sf
    import numpy as np
    HAS_AUDIO = True
except:
    HAS_AUDIO = False

# MIDI backends
try:
    import mido  # macOS/Linux backend via python-rtmidi
    HAS_MIDI_MIDO = True
    debug_log("MIDI: mido available (rtmidi backend expected on macOS)")
except:
    HAS_MIDI_MIDO = False
    debug_log("MIDI: mido not available")

# Windows native MIDI support via ctypes
try:
    import ctypes
    import ctypes.wintypes
    HAS_WINDOWS_MIDI = True
    debug_log("MIDI: Windows native MIDI available")
except:
    HAS_WINDOWS_MIDI = False

HAS_MIDI = HAS_WINDOWS_MIDI or HAS_MIDI_MIDO


class TimelineEditorGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Timeline Editor - DMX Art-Net Recorder/Player")
        # Optional splash banner with logo shown briefly on startup
        try:
            # Briefly hide the main window so only the splash is visible
            try:
                self.root.withdraw()
            except Exception:
                pass
            self._show_splash_banner()
        except Exception:
            pass
        self.root.geometry("1400x800")
        try:
            self.root.state("zoomed")  # Start maximized on Windows
        except Exception:
            pass
        
        self.timeline_data = None
        self.is_playing = False
        self.playhead_pos = 0.0
        self.zoom_level = 100
        self.selected_universe = 0
        self.dmx_values = {}
        self.dmx_monitor_running = True
        self.recording = False
        self.recorded_events = []
        self.capture_session = 0  # Increment per recording
        self.current_session_id = 0
        self.session_palette = [
            "#64b5f6", "#ba68c8", "#ffb74d", "#81c784",
            "#4dd0e1", "#f06292", "#aed581", "#ff8a65"
        ]
        self.session_bounds = {}
        self.selected_session = None
        self.audio_file = None
        self.audio_data = None
        self.audio_duration = 0.0
        self.play_obj = None
        self.waveform_cached = False  # Cache flag to avoid redrawing waveform
        
        # Art-Net frame selection
        self.selected_frame = None
        self.frame_boxes = {}  # Map frame index to canvas box coordinates
        
        # Drag-to-zoom
        self.drag_start = None
        self.zoom_box_id = None
        self.drag_threshold_distance = 5  # pixels before treating as drag
        self.is_dragging = False
        
        # Playhead dragging
        self.dragging_playhead = False
        # Session dragging to shift all frames in a session
        self._dragging_session_id = None
        self._session_drag_start_x = None
        self._session_times_snapshot = None
        # MIDI marker dragging
        self.drag_midi_index = None
        self._drag_midi_ref = None
        self._midi_drag_dt = 0.0
        
        # DMX monitor visibility
        self.monitor_visible = True

        # Capture indicator state
        self._set_record_indicator(False)
        
        # DMX value cache for optimization
        self._last_dmx_values = {}
        
        # Undo/Redo stacks
        self.undo_stack = []
        self.redo_stack = []
        self.max_undo_levels = 50
        
        # Session names
        self.session_names = {}  # {session_id: "name"}
        
        # Timeline markers
        self.markers = []  # [{"t": time, "label": "name"}]
        
        # MIDI markers
        self.midi_markers = []  # [{"t": time, "note": int, "velocity": int, "channel": int, "duration": float}]
        # OSC markers
        self.osc_markers = []  # [{"t": time, "name": str, "ip": str, "port": int, "address": str, "args": list}]
        # Selection/drag state for OSC
        self.selected_osc_marker = None
        self.drag_osc_index = None
        self._drag_osc_ref = None
        self._osc_drag_dt = 0.0
        self.selected_midi_marker = None
        
        # Loop region
        self.loop_enabled = False
        self.loop_start = 0.0
        self.loop_end = 0.0
        
        # DMX channel filter
        self.dmx_filter_enabled = False
        self.dmx_filter_channels = list(range(512))  # All channels by default
        
        # DMX universe filter - load from config file if exists
        self.universe_filter_enabled = False
        self.universe_filter_list = [0]  # Capture universe 0 by default
        
        # Load DMX filter config
        try:
            import json
            config_file = "dmx_filter_config.json"
            if os.path.exists(config_file):
                with open(config_file, 'r') as f:
                    config = json.load(f)
                    self.universe_filter_enabled = config.get("universe_filter_enabled", False)
                    self.universe_filter_list = config.get("universe_filter_list", [0])
                    self.dmx_filter_enabled = config.get("dmx_filter_enabled", False)
                    self.dmx_filter_channels = config.get("dmx_filter_channels", list(range(512)))
        except Exception as e:
            print(f"Error loading config: {e}")

        # Default monitor universe follows the filter if enabled; otherwise use universe 1
        if self.universe_filter_enabled and self.universe_filter_list:
            self.selected_universe = int(self.universe_filter_list[0])
        else:
            self.selected_universe = 1
        
        # Settings
        self.settings_file = os.path.join(os.path.expanduser("~"), ".timeline_settings.json")
        self.settings = self._load_settings()
        self.network_interface = self.settings.get("network_interface", "0.0.0.0")
        self.audio_device = self.settings.get("audio_device", None)
        self.midi_output_port = self.settings.get("midi_output_port", None)
        self.midi_port = None  # Will be opened when needed
        # Ignore-on-Capture for DMX (learn active channels)
        self.ignored_on_capture_enabled = False
        self.ignored_on_capture = {}
        self.ignored_baseline = {}
        # Session priority (advanced): enable flag and per-session priorities
        self.session_priority_enabled = False
        self.session_priorities = {}
        self.windows_midi_handle = None  # Windows MIDI device handle
        self.last_sent_midi = {}  # Track last sent MIDI markers to avoid duplicates
        # OSC playback helpers
        self.last_sent_osc = {}
        self._osc_clients = {}
        self._osc_sockets = {}  # cache sockets bound to selected OSC interface per target
        # Recent OSC target IPs (for quick selection in dialogs)
        self.recent_osc_ips = []
        # Last-used MIDI test params (persisted)
        self.last_test_midi_note = self.settings.get("last_test_midi_note", 60)
        self.last_test_midi_channel = self.settings.get("last_test_midi_channel", 1)
        # Logging verbosity
        self.verbose_logging = bool(self.settings.get("verbose_logging", False))
        try:
            set_verbose_logging(self.verbose_logging)
        except Exception:
            pass
        # Log app start to both logs
        try:
            debug_log("APP START: Timeline GUI launching")
            # Ensure debug.txt exists and record start even if verbose is off
            ts = __import__("datetime").datetime.now().astimezone().isoformat()
            line = f"{ts} APP START (verbose={'on' if self.verbose_logging else 'off'})\n"
            try:
                # Ensure directory exists
                try:
                    os.makedirs(os.path.dirname(_VERBOSE_FILE), exist_ok=True)
                except Exception:
                    pass
                with open(_VERBOSE_FILE, "a", encoding="utf-8", errors="replace") as df:
                    df.write(line)
                    try:
                        df.flush()
                        os.fsync(df.fileno())
                    except Exception:
                        pass
                # Also write which MIDI backends are available
                try:
                    if HAS_WINDOWS_MIDI:
                        debug_log("MIDI BACKEND: winmm available")
                    if HAS_MIDI_MIDO:
                        debug_log("MIDI BACKEND: mido available")
                    if not (HAS_WINDOWS_MIDI or HAS_MIDI_MIDO):
                        debug_log("MIDI BACKEND: none available")
                except Exception:
                    pass
            except Exception:
                pass
        except Exception:
            pass
        # Window geometry persistence
        self.window_width = int(self.settings.get("window_width", 1400))
        self.window_height = int(self.settings.get("window_height", 800))
        self.window_maximized = bool(self.settings.get("window_maximized", True))
        # Sash persistence: store both ratio and pixel
        self.monitor_sash_ratio = float(self.settings.get("monitor_sash_ratio", 0.7))
        self.monitor_sash_left_px = int(self.settings.get("monitor_sash_left_px", 0))
        
        # Store availability flags as instance variables
        self.has_midi = HAS_MIDI
        self.has_audio = HAS_AUDIO
        
        # Splash settings
        self.splash_enabled = bool(self.settings.get("splash_enabled", True))
        self.splash_duration_ms = int(self.settings.get("splash_duration_ms", 10000))

        self._check_audio_dependencies()
        # Update build_info.json at startup so About shows recent build/run time
        try:
            here = os.path.dirname(__file__)
            bi_path = os.path.join(here, "build_info.json")
            import datetime
            # Write local time for clarity
            local_now = datetime.datetime.now().astimezone()
            info = {"build_time": local_now.isoformat()}
            with open(bi_path, "w", encoding="utf-8") as f:
                import json
                json.dump(info, f, indent=2)
        except Exception:
            pass
        self._setup_ui()
        # Bind keyboard shortcut for adding OSC marker ('o')
        try:
            self.root.bind("<KeyPress-o>", lambda e: self._add_osc_marker())
        except Exception:
            pass
        # Restore window geometry before sash placement
        def _restore_window_geometry():
            try:
                if self.window_maximized:
                    try:
                        self.root.state("zoomed")
                    except Exception:
                        pass
                else:
                    self.root.geometry(f"{self.window_width}x{self.window_height}")
            except Exception:
                pass
        self.root.after(100, _restore_window_geometry)
        self._start_dmx_monitor()

    def _show_splash_banner(self):
        """Show a simple splash banner with logo before the UI loads."""
        try:
            if not getattr(self, "splash_enabled", True):
                return
            # Ensure geometry info is up-to-date so centering works reliably
            try:
                self.root.update_idletasks()
            except Exception:
                pass
            splash = tk.Toplevel(self.root)
            # Withdraw first to avoid on-screen resize flicker while we compute geometry
            try:
                splash.withdraw()
            except Exception:
                pass
            splash.overrideredirect(True)
            splash.configure(bg="#ffffff")
            # Precompute target size (default or logo-based) before showing the window
            default_w, default_h = 460, 260
            target_w, target_h = default_w, default_h

            # Simple content frame (no border)
            frame = tk.Frame(splash, bg="#ffffff")
            # Try to load logo image next to the script (png recommended)
            logo_path_candidates = [
                os.path.join(os.path.dirname(__file__), "logo.png"),
                os.path.join(os.path.dirname(__file__), "assets", "logo.png"),
                os.path.join(os.path.dirname(os.path.dirname(__file__)), "logo.png"),
            ]
            logo_img = None
            for p in logo_path_candidates:
                if os.path.exists(p):
                    # Try Tk's native PhotoImage first (no PIL required)
                    try:
                        logo_img = tk.PhotoImage(file=p)
                        # Optionally subsample if extremely large
                        try:
                            if logo_img.width() > 640:
                                logo_img = logo_img.subsample(max(1, logo_img.width() // 320))
                        except Exception:
                            pass
                        break
                    except Exception:
                        # Fallback to PIL if available
                        try:
                            from PIL import Image, ImageTk
                            img = Image.open(p)
                            img = img.convert("RGBA")
                            max_w, max_h = 320, 120
                            img.thumbnail((max_w, max_h))
                            logo_img = ImageTk.PhotoImage(img)
                            break
                        except Exception:
                            logo_img = None
                            # continue checking other candidate paths

            if logo_img is not None:
                # If we have a logo, compute splash size to match logo dimensions with padding
                try:
                    logo_w = int(logo_img.width())
                    logo_h = int(logo_img.height())
                    pad_top = 32
                    pad_bottom = 12
                    # Provide more vertical room to ensure text never clips
                    text_block_h = 72
                    target_w = max(logo_w + 48, 320)  # side padding
                    target_h = max(logo_h + pad_top + pad_bottom + text_block_h, 200)
                except Exception:
                    target_w, target_h = default_w, default_h
                tk.Label(frame, image=logo_img, bg="#ffffff").pack(pady=(32, 8))
                # Keep reference to avoid GC
                splash.logo_img = logo_img
            else:
                tk.Label(frame, text="Timeline", fg="#000000", bg="#ffffff", font=("Segoe UI", 28, "bold")).pack(pady=(40, 10))

            tk.Label(frame, text="Art-Net DMX Recorder & Player", fg="#333333", bg="#ffffff", font=("Segoe UI", 11)).pack()
            tk.Label(frame, text="Loading…", fg="#555555", bg="#ffffff", font=("Segoe UI", 10)).pack(pady=(14, 0))

            # Pack content normally without custom border
            try:
                frame.pack(fill=tk.BOTH, expand=True)
            except Exception:
                pass

            # Set final geometry once and show the splash to avoid resize flicker
            try:
                # Ensure metrics are available
                splash.update_idletasks()
                sx = (splash.winfo_screenwidth() // 2) - (target_w // 2)
                sy = (splash.winfo_screenheight() // 2) - (target_h // 2)
                splash.geometry(f"{target_w}x{target_h}+{sx}+{sy}")
                splash.deiconify()
                # Now raise and keep on top to avoid stacking issues
                try:
                    splash.attributes("-topmost", True)
                    splash.lift()
                except Exception:
                    pass
                # Force an immediate draw so logo appears without delay
                try:
                    splash.update()
                except Exception:
                    pass
            except Exception:
                pass

            # Close splash after short delay and before building the rest of UI
            def _close_splash():
                try:
                    splash.destroy()
                    # Bring main window to foreground once splash closes
                    try:
                        self.root.deiconify()
                        self.root.lift()
                        self.root.focus_force()
                    except Exception:
                        pass
                except Exception:
                    pass
            # Show for configured duration
            try:
                dur = int(getattr(self, "splash_duration_ms", 4000))
            except Exception:
                dur = 4000
            self.root.after(max(300, dur), _close_splash)
            # Allow user to dismiss early by click or key
            try:
                splash.bind("<Button-1>", lambda e: _close_splash())
                splash.bind("<Key>", lambda e: _close_splash())
            except Exception:
                pass
        except Exception:
            pass
    def _set_record_indicator(self, active: bool):
        """Update capture indicator label color/text."""
        if not hasattr(self, "capture_indicator"):
            return
        if active:
            self.capture_indicator.config(text="CAPTURE ON", bg="#c62828", fg="white")
        else:
            self.capture_indicator.config(text="CAPTURE OFF", bg="#2b2b2b", fg="lightgray")

    def _show_status(self, message: str, timeout: float = 1.5):
        """Show a transient status message near the bottom of the window."""
        try:
            # Avoid logging tooltip/status messages to debug to reduce noise
            # Skip messages that look like tips or transient UI hints
            try:
                if not (message.startswith("Tip:") or message.startswith("TIP:") or message.startswith("Hint:") or message.startswith("HINT:")):
                    debug_log(f"STATUS: {message}")
            except Exception:
                pass
            if not hasattr(self, "_status_label"):
                self._status_label = tk.Label(self.root, text="", bg="#333", fg="white", font=("Arial", 9))
                self._status_label.place(relx=0.5, rely=0.98, anchor="s")
            self._status_label.config(text=message)
            # Hide after timeout
            def hide():
                try:
                    self._status_label.config(text="")
                except Exception:
                    pass
            self.root.after(int(timeout * 1000), hide)
        except Exception:
            pass

    def _flash_midi_activity(self):
        """Flash a small MIDI activity indicator in the main UI."""
        try:
            # Ensure monitor activity widgets exist if monitor_frame is available
            try:
                if hasattr(self, "monitor_frame") and self.monitor_frame:
                    if not hasattr(self, "monitor_activity_frame") or self.monitor_activity_frame is None:
                        # Build minimal activity UI if missing
                        self.monitor_activity_frame = tk.Frame(self.monitor_frame, bg="#ffffff")
                        self.monitor_midi_col = tk.Frame(self.monitor_activity_frame, bg="#ffffff")
                        self.monitor_midi_light = tk.Label(self.monitor_midi_col, text="MIDI", width=6,
                                                           bg="#dddddd", fg="#222222", font=("Segoe UI", 9, "bold"),
                                                           relief="groove")
                        self.monitor_midi_last_label = tk.Label(self.monitor_midi_col, text="—", bg="#ffffff",
                                                                fg="#333333", font=("Segoe UI", 9))
                        self.monitor_midi_light.pack(fill="x", padx=8, pady=(0, 2))
                        self.monitor_midi_last_label.pack(fill="x", padx=8, pady=(0, 6))
                        self.monitor_osc_col = tk.Frame(self.monitor_activity_frame, bg="#ffffff")
                        self.monitor_osc_light = tk.Label(self.monitor_osc_col, text="OSC", width=6,
                                                          bg="#dddddd", fg="#222222", font=("Segoe UI", 9, "bold"),
                                                          relief="groove")
                        self.monitor_osc_last_label = tk.Label(self.monitor_osc_col, text="—", bg="#ffffff",
                                                               fg="#333333", font=("Segoe UI", 9))
                        self.monitor_osc_light.pack(fill="x", padx=8, pady=(0, 2))
                        self.monitor_osc_last_label.pack(fill="x", padx=8, pady=(0, 6))
                        self.monitor_midi_col.pack(side="left", fill="x", expand=True)
                        self.monitor_osc_col.pack(side="left", fill="x", expand=True)
                        self.monitor_activity_frame.pack(fill="x")
            except Exception:
                pass
            # Remove legacy top-right MIDI indicator if present; use monitor lights only
            try:
                if hasattr(self, "_midi_indicator") and self._midi_indicator:
                    self._midi_indicator.destroy()
                    self._midi_indicator = None
            except Exception:
                pass
            def do_flash():
                try:
                    if hasattr(self, "monitor_midi_light") and self.monitor_midi_light:
                        self.monitor_midi_light.config(bg="#b2ff59")
                    if hasattr(self, "_last_midi_note_text") and hasattr(self, "monitor_midi_last_label"):
                        self.monitor_midi_last_label.config(text=self._last_midi_note_text)
                except Exception:
                    pass
            def reset():
                try:
                    if hasattr(self, "monitor_midi_light") and self.monitor_midi_light:
                        self.monitor_midi_light.config(bg="#dddddd")
                except Exception:
                    pass
            # Ensure UI updates happen on the Tk main thread
            self.root.after(0, do_flash)
            self.root.after(200, reset)
        except Exception:
            pass

    def _flash_osc_activity(self, message_text: str):
        """Flash OSC activity in the monitor and record last message text."""
        try:
            # Ensure monitor activity widgets exist if monitor_frame is available
            try:
                if hasattr(self, "monitor_frame") and self.monitor_frame:
                    if not hasattr(self, "monitor_activity_frame") or self.monitor_activity_frame is None:
                        # Build minimal activity UI if missing
                        self.monitor_activity_frame = tk.Frame(self.monitor_frame, bg="#ffffff")
                        self.monitor_midi_col = tk.Frame(self.monitor_activity_frame, bg="#ffffff")
                        self.monitor_midi_light = tk.Label(self.monitor_midi_col, text="MIDI", width=6,
                                                           bg="#dddddd", fg="#222222", font=("Segoe UI", 9, "bold"),
                                                           relief="groove")
                        self.monitor_midi_last_label = tk.Label(self.monitor_midi_col, text="—", bg="#ffffff",
                                                                fg="#333333", font=("Segoe UI", 9))
                        self.monitor_midi_light.pack(fill="x", padx=8, pady=(0, 2))
                        self.monitor_midi_last_label.pack(fill="x", padx=8, pady=(0, 6))
                        self.monitor_osc_col = tk.Frame(self.monitor_activity_frame, bg="#ffffff")
                        self.monitor_osc_light = tk.Label(self.monitor_osc_col, text="OSC", width=6,
                                                          bg="#dddddd", fg="#222222", font=("Segoe UI", 9, "bold"),
                                                          relief="groove")
                        self.monitor_osc_last_label = tk.Label(self.monitor_osc_col, text="—", bg="#ffffff",
                                                               fg="#333333", font=("Segoe UI", 9))
                        self.monitor_osc_light.pack(fill="x", padx=8, pady=(0, 2))
                        self.monitor_osc_last_label.pack(fill="x", padx=8, pady=(0, 6))
                        self.monitor_midi_col.pack(side="left", fill="x", expand=True)
                        self.monitor_osc_col.pack(side="left", fill="x", expand=True)
                        self.monitor_activity_frame.pack(fill="x")
            except Exception:
                pass
            def do_flash():
                try:
                    # Update last-message label
                    self._last_osc_text = message_text
                    if hasattr(self, "monitor_osc_last_label") and self.monitor_osc_last_label:
                        self.monitor_osc_last_label.config(text=message_text)
                    # Flash light
                    if hasattr(self, "monitor_osc_light") and self.monitor_osc_light:
                        self.monitor_osc_light.config(bg="#80d8ff")  # light blue
                except Exception:
                    pass
            def reset():
                try:
                    if hasattr(self, "monitor_osc_light") and self.monitor_osc_light:
                        self.monitor_osc_light.config(bg="#dddddd")
                except Exception:
                    pass
            # Ensure UI updates happen on the Tk main thread
            self.root.after(0, do_flash)
            self.root.after(200, reset)
        except Exception:
            pass
    
    def _check_audio_dependencies(self):
        """Check if audio libraries are available."""
        try:
            import mutagen
            import soundfile
            self.has_audio = True
        except:
            self.has_audio = False

    def _new_timeline(self):
        """Reset timeline and recording state to start a new project."""
        self.is_playing = False
        self.recording = False
        self._stop_audio()
        self.timeline_data = []
        self.recorded_events = []
        self.selected_frame = None
        self.selected_session = None
        self.session_bounds = {}
        self.playhead_pos = 0.0
        self.waveform_cached = False
        # Clear capture sessions
        self.capture_session = 0
        self.current_session_id = 0
        # Clear undo/redo, session names, and markers
        self.undo_stack = []
        self.redo_stack = []
        self.session_names = {}
        self.markers = []
        self.midi_markers = []
        self.selected_midi_marker = None
        # Clear loop region
        self.loop_enabled = False
        self.loop_start = 0.0
        self.loop_end = 0.0
        # Clear audio file
        self.audio_file = None
        self.audio_data = None
        self.audio_duration = 0.0
        self.audio_label.config(text="None", foreground="cyan")
        self._update_canvas_view()
    
    def _save_undo_state(self):
        """Save current state to undo stack."""
        state = {
            "timeline_data": [evt.copy() for evt in self.timeline_data] if self.timeline_data else [],
            "session_names": self.session_names.copy(),
            "markers": [m.copy() for m in self.markers],
            "midi_markers": [m.copy() for m in self.midi_markers]
        }
        self.undo_stack.append(state)
        if len(self.undo_stack) > self.max_undo_levels:
            self.undo_stack.pop(0)
        # Clear redo stack when new action is taken
        self.redo_stack = []
    
    def _undo(self):
        """Undo last action."""
        if not self.undo_stack:
            return
        
        # Save current state to redo stack
        current_state = {
            "timeline_data": [evt.copy() for evt in self.timeline_data] if self.timeline_data else [],
            "session_names": self.session_names.copy(),
            "markers": [m.copy() for m in self.markers],
            "midi_markers": [m.copy() for m in self.midi_markers]
        }
        self.redo_stack.append(current_state)
        
        # Restore previous state
        state = self.undo_stack.pop()
        self.timeline_data = state["timeline_data"]
        self.session_names = state["session_names"]
        self.markers = state["markers"]
        self.waveform_cached = False
        self._update_canvas_view()
    
    def _redo(self):
        """Redo last undone action."""
        if not self.redo_stack:
            return
        
        # Save current state to undo stack
        current_state = {
            "timeline_data": [evt.copy() for evt in self.timeline_data] if self.timeline_data else [],
            "session_names": self.session_names.copy(),
            "markers": [m.copy() for m in self.markers],
            "midi_markers": [m.copy() for m in self.midi_markers]
        }
        self.undo_stack.append(current_state)
        
        # Restore redo state
        state = self.redo_stack.pop()
        self.timeline_data = state["timeline_data"]
        self.session_names = state["session_names"]
        self.markers = state["markers"]
        self.midi_markers = state.get("midi_markers", [])
        self.waveform_cached = False
        self._update_canvas_view()
    
    def _rename_session(self):
        """Rename a selected session."""
        if self.selected_session is None:
            messagebox.showwarning("Rename Session", "Please select a session first by clicking on it.")
            return
        
        s_id = self.selected_session
        current_name = self.session_names.get(s_id, f"Session {s_id}")
        
        dialog = tk.Toplevel(self.root)
        dialog.title(f"Rename Session {s_id}")
        dialog.geometry("400x150")
        dialog.configure(bg="gray20")
        dialog.transient(self.root)
        dialog.grab_set()
        
        tk.Label(dialog, text=f"Enter new name for Session {s_id}:", bg="gray20", fg="white", font=("Arial", 10)).pack(pady=10)
        
        name_var = tk.StringVar(value=current_name)
        name_entry = tk.Entry(dialog, textvariable=name_var, bg="gray40", fg="white", width=40, font=("Arial", 10))
        name_entry.pack(pady=10)
        name_entry.select_range(0, tk.END)
        name_entry.focus()
        
        def save_name():
            new_name = name_var.get().strip()
            if new_name:
                self._save_undo_state()
                self.session_names[s_id] = new_name
                self.waveform_cached = False
                self._update_canvas_view()
                dialog.destroy()
        
        button_frame = tk.Frame(dialog, bg="gray20")
        button_frame.pack(pady=10)
        tk.Button(button_frame, text="Save", command=save_name, bg="gray40", fg="white", width=10).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Cancel", command=dialog.destroy, bg="gray40", fg="white", width=10).pack(side=tk.LEFT, padx=5)
        
        name_entry.bind("<Return>", lambda e: save_name())
        name_entry.bind("<Escape>", lambda e: dialog.destroy())
    
    def _add_marker(self):
        """Add a marker at current playhead position."""
        dialog = tk.Toplevel(self.root)
        dialog.title("Add Marker")
        dialog.geometry("400x150")
        dialog.configure(bg="gray20")
        dialog.transient(self.root)
        dialog.grab_set()
        
        label_var = tk.StringVar(value="Marker")
        label_entry = tk.Entry(dialog, textvariable=label_var, bg="gray40", fg="white", width=40, font=("Arial", 10))
        label_entry.select_range(0, tk.END)
        label_entry.focus()
        
        def save_marker():
            label = label_var.get().strip()
            if label:
                self._save_undo_state()
                self.markers.append({"t": self.playhead_pos, "label": label})
                self.markers.sort(key=lambda m: m["t"])
                self.waveform_cached = False
                self._update_canvas_view()
                dialog.destroy()
        
        button_frame = tk.Frame(dialog, bg="gray20")
        button_frame.pack(pady=10)
        tk.Button(button_frame, text="Add", command=save_marker, bg="gray40", fg="white", width=10).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Cancel", command=dialog.destroy, bg="gray40", fg="white", width=10).pack(side=tk.LEFT, padx=5)
        
        label_entry.bind("<Return>", lambda e: save_marker())
        label_entry.bind("<Escape>", lambda e: dialog.destroy())
    
    def _delete_marker(self):
        """Delete marker closest to playhead."""
        if not self.markers:
            messagebox.showwarning("Delete Marker", "No markers to delete")
            return
        
        # Find closest marker to playhead
        closest_marker = min(self.markers, key=lambda m: abs(m["t"] - self.playhead_pos))
        
        if abs(closest_marker["t"] - self.playhead_pos) > 5.0:
            messagebox.showwarning("Delete Marker", "No marker found near playhead position")
            return
        
        self._save_undo_state()
        self.markers.remove(closest_marker)
        self.waveform_cached = False
        self._update_canvas_view()
    
    def _set_loop_in(self):
        """Set loop in point at current playhead position."""
        self.loop_start = self.playhead_pos
        if self.loop_end <= self.loop_start:
            self.loop_end = self.loop_start + 5.0  # Default 5 second region
        self.loop_enabled = True
        self.waveform_cached = False
        self._update_canvas_view()
    
    def _set_loop_out(self):
        """Set loop out point at current playhead position."""
        self.loop_end = self.playhead_pos
        if self.loop_end <= self.loop_start:
            self.loop_start = max(0, self.loop_end - 5.0)  # Default 5 second region
        self.loop_enabled = True
        self.waveform_cached = False
        self._update_canvas_view()
    
    def _toggle_loop(self):
        """Toggle loop playback on/off."""
        self.loop_enabled = not self.loop_enabled
        self.waveform_cached = False
        self._update_canvas_view()
    
    def _clear_loop(self):
        """Clear loop region."""
        self.loop_enabled = False
        self.loop_start = 0.0
        self.loop_end = 0.0
        self.waveform_cached = False
        self._update_canvas_view()
    
    def _add_midi_marker(self):
        """Add a MIDI marker at current playhead position."""
        dialog = tk.Toplevel(self.root)
        dialog.title("Add MIDI Marker")
        dialog.geometry("500x300")
        dialog.configure(bg="gray20")
        dialog.transient(self.root)
        dialog.grab_set()
        
        tk.Label(dialog, text=f"Add MIDI marker at {self._format_time(self.playhead_pos)}:", 
                bg="gray20", fg="white", font=("Arial", 10, "bold")).pack(pady=10)
        
        # Create form frame
        form_frame = tk.Frame(dialog, bg="gray20")
        form_frame.pack(pady=10, padx=20, fill=tk.BOTH)
        
        # Note
        tk.Label(form_frame, text="MIDI Note (0-127):", bg="gray20", fg="white").grid(row=0, column=0, sticky="w", pady=5)
        note_var = tk.IntVar(value=60)  # Middle C
        note_spin = tk.Spinbox(form_frame, from_=0, to=127, textvariable=note_var, bg="gray40", fg="white", width=15)
        note_spin.grid(row=0, column=1, pady=5, padx=10)
        
        # Velocity
        tk.Label(form_frame, text="Velocity (0-127):", bg="gray20", fg="white").grid(row=1, column=0, sticky="w", pady=5)
        velocity_var = tk.IntVar(value=100)
        velocity_spin = tk.Spinbox(form_frame, from_=0, to=127, textvariable=velocity_var, bg="gray40", fg="white", width=15)
        velocity_spin.grid(row=1, column=1, pady=5, padx=10)
        
        # Channel
        tk.Label(form_frame, text="MIDI Channel (1-16):", bg="gray20", fg="white").grid(row=2, column=0, sticky="w", pady=5)
        channel_var = tk.IntVar(value=1)
        channel_spin = tk.Spinbox(form_frame, from_=1, to=16, textvariable=channel_var, bg="gray40", fg="white", width=15)
        channel_spin.grid(row=2, column=1, pady=5, padx=10)
        
        # Duration
        tk.Label(form_frame, text="Duration (seconds):", bg="gray20", fg="white").grid(row=3, column=0, sticky="w", pady=5)
        duration_var = tk.DoubleVar(value=0.1)
        duration_spin = tk.Spinbox(form_frame, from_=0.01, to=10.0, increment=0.1, textvariable=duration_var, 
                                   bg="gray40", fg="white", width=15)
        duration_spin.grid(row=3, column=1, pady=5, padx=10)
        
        # Label (optional)
        tk.Label(form_frame, text="Label (optional):", bg="gray20", fg="white").grid(row=4, column=0, sticky="w", pady=5)
        label_var = tk.StringVar(value="")
        label_entry = tk.Entry(form_frame, textvariable=label_var, bg="gray40", fg="white", width=25)
        label_entry.grid(row=4, column=1, pady=5, padx=10)
        
        # Learn MIDI button: detect incoming MIDI and set fields
        def learn_midi():
            try:
                if not HAS_WINDOWS_MIDI:
                    messagebox.showinfo("MIDI Learn", "Windows MIDI not available on this system.")
                    return
                # Enumerate Windows MIDI input devices using winmm
                winmm = ctypes.windll.winmm
                num_devs = winmm.midiInGetNumDevs()
                devices = []
                class MIDIINCAPS(ctypes.Structure):
                    _fields_ = [
                        ("wMid", ctypes.wintypes.WORD),
                        ("wPid", ctypes.wintypes.WORD),
                        ("vDriverVersion", ctypes.wintypes.DWORD),
                        ("szPname", ctypes.c_wchar * 32),
                        ("dwSupport", ctypes.wintypes.DWORD),
                    ]
                for i in range(num_devs):
                    caps = MIDIINCAPS()
                    res = winmm.midiInGetDevCapsW(i, ctypes.byref(caps), ctypes.sizeof(caps))
                    if res == 0:
                        devices.append(f"[{i}] {caps.szPname}")
                if not devices:
                    messagebox.showinfo("MIDI Learn", "No Windows MIDI input devices found.")
                    return

                # Selection dialog
                sel = tk.Toplevel(dialog)
                sel.title("Select Windows MIDI Input")
                sel.geometry("420x260")
                sel.configure(bg="gray20")
                tk.Label(sel, text="Select an input device to learn from:", bg="gray20", fg="white").pack(pady=8)
                in_var = tk.StringVar(value=devices[0])
                list_frame = tk.Frame(sel, bg="gray20")
                list_frame.pack(fill=tk.BOTH, expand=True)
                for nm in devices:
                    ttk.Radiobutton(list_frame, text=nm, variable=in_var, value=nm).pack(anchor="w", pady=2)

                def start_learn_winmm():
                    try:
                        dev_label = in_var.get()
                        dev_id = int(dev_label.split("]")[0].strip("["))
                        sel.destroy()

                        # Define callback type with 64-bit safe pointer sizes:
                        # void CALLBACK(HMIDIIN, UINT, DWORD_PTR, DWORD_PTR, DWORD_PTR)
                        DWORD_PTR = ctypes.c_size_t
                        CALLBACK = ctypes.WINFUNCTYPE(None, ctypes.wintypes.HANDLE, ctypes.wintypes.UINT, DWORD_PTR, DWORD_PTR, DWORD_PTR)

                        learned = {"done": False}

                        def midi_in_callback(hMidiIn, wMsg, dwInstance, dwParam1, dwParam2):
                            MIM_DATA = 0x3C3
                            try:
                                debug_log(f"LEARN: callback wMsg=0x{wMsg:X} dwParam1=0x{dwParam1:X} dwParam2=0x{dwParam2:X}")
                            except Exception:
                                pass
                            if wMsg == MIM_DATA and not learned["done"]:
                                msg = dwParam1
                                status = msg & 0xFF
                                note = (msg >> 8) & 0xFF
                                velocity = (msg >> 16) & 0xFF
                                status_type = status & 0xF0
                                channel = (status & 0x0F) + 1
                                debug_log(f"LEARN: parsed status=0x{status:02X} type=0x{status_type:02X} note={note} vel={velocity} ch={channel}")
                                # Append to live log in UI
                                def add_log():
                                    try:
                                        log_list.insert(tk.END, f"status=0x{status:02X} type=0x{status_type:02X} note={note} vel={velocity} ch={channel}")
                                        log_list.see(tk.END)
                                    except Exception:
                                        pass
                                self.root.after(0, add_log)
                                if status_type == 0x90 and velocity > 0:
                                    # Update UI on main thread
                                    def apply_values():
                                        note_var.set(int(note))
                                        velocity_var.set(int(velocity))
                                        channel_var.set(int(channel))
                                        self._show_status(f"Learned note {note} ch {channel}")
                                    self.root.after(0, apply_values)
                                    learned["done"] = True
                                else:
                                    # If first message is not note_on, still surface it to user
                                    def show_info():
                                        self._show_status(f"Received MIDI status=0x{status:02X} note={note} vel={velocity}")
                                    self.root.after(0, show_info)

                        cb = CALLBACK(midi_in_callback)
                        # Keep reference to prevent GC while device is open
                        self._midi_in_cb = cb

                        # Show non-blocking listening status dialog with cancel
                        listen = tk.Toplevel(dialog)
                        listen.title("Listening for MIDI…")
                        listen.geometry("320x180")
                        listen.configure(bg="gray20")
                        tk.Label(listen, text="Play a note on your MIDI device",
                                 bg="gray20", fg="white").pack(pady=10)
                        # Live log of captured messages
                        log_frame = tk.Frame(listen, bg="gray20")
                        log_frame.pack(fill=tk.BOTH, expand=True, padx=8)
                        log_list = tk.Listbox(log_frame, height=4)
                        log_list.pack(fill=tk.BOTH, expand=True)
                        cancel_flag = {"stop": False}
                        def cancel_listen():
                            cancel_flag["stop"] = True
                            listen.destroy()
                        ttk.Button(listen, text="Cancel", command=cancel_listen).pack(pady=6)

                        hIn = ctypes.c_void_p()
                        res_open = winmm.midiInOpen(ctypes.byref(hIn), dev_id, cb, 0, 0x00030000)
                        if res_open != 0:
                            listen.destroy()
                            messagebox.showerror("MIDI Learn Failed", f"Failed to open device {dev_id}, code={res_open}")
                            return
                        debug_log(f"LEARN: opened device id={dev_id}, code={res_open}, handle={hIn}")
                        rc_start = winmm.midiInStart(hIn)
                        debug_log(f"LEARN: midiInStart rc={rc_start}")
                        # Store handle to keep it alive during learn
                        self._midi_in_handle = hIn

                        def worker():
                            try:
                                deadline = time.time() + 10.0
                                while time.time() < deadline and not learned["done"] and not cancel_flag["stop"]:
                                    time.sleep(0.02)
                            finally:
                                try:
                                    rc_stop = winmm.midiInStop(hIn)
                                    rc_reset = winmm.midiInReset(hIn)
                                    rc_close = winmm.midiInClose(hIn)
                                    debug_log(f"LEARN: midiInStop rc={rc_stop}, reset rc={rc_reset}, close rc={rc_close}")
                                except Exception:
                                    pass
                                # Clear stored references
                                try:
                                    self._midi_in_handle = None
                                    self._midi_in_cb = None
                                except Exception:
                                    pass
                                # Close the listening dialog if still open
                                try:
                                    self.root.after(0, listen.destroy)
                                except Exception:
                                    pass
                                if not learned["done"] and not cancel_flag["stop"]:
                                    self.root.after(0, lambda: messagebox.showinfo("MIDI Learn", "No note detected within 10 seconds."))

                        threading.Thread(target=worker, daemon=True).start()
                    except Exception as e:
                        messagebox.showerror("MIDI Learn Failed", str(e))

                ttk.Button(sel, text="Start Learn", command=start_learn_winmm).pack(pady=10)
                ttk.Button(sel, text="Cancel", command=sel.destroy).pack()
            except Exception as e:
                messagebox.showerror("MIDI Learn Error", str(e))

        def save_midi_marker():
            try:
                note = note_var.get()
                velocity = velocity_var.get()
                channel = channel_var.get()
                duration = duration_var.get()
                label = label_var.get().strip()
                
                self._save_undo_state()
                midi_marker = {
                    "t": self.playhead_pos,
                    "note": note,
                    "velocity": velocity,
                    "channel": channel,
                    "duration": duration,
                    "label": label
                }
                self.midi_markers.append(midi_marker)
                self.midi_markers.sort(key=lambda m: m["t"])
                self.waveform_cached = False
                self._update_canvas_view()
                dialog.destroy()
            except Exception as e:
                messagebox.showerror("Error", f"Invalid MIDI parameters: {e}")
        
        button_frame = tk.Frame(dialog, bg="gray20")
        button_frame.pack(pady=10)
        def test_current_midi():
            try:
                if not self.midi_output_port:
                    messagebox.showwarning("MIDI", "Select a MIDI output device in Settings first")
                    return
                n = int(note_var.get())
                v = int(velocity_var.get())
                ch = int(channel_var.get())
                dur = float(duration_var.get())
                # Route through standard sender (uses Windows backend here)
                self._send_midi_note(n, v, ch, max(0.01, dur))
                try:
                    self._show_status(f"Tested MIDI note {n} ch {ch}")
                except Exception:
                    pass
            except Exception as e:
                messagebox.showerror("MIDI Test Failed", str(e))

        tk.Button(button_frame, text="Add", command=save_midi_marker, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Test MIDI", command=test_current_midi, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Learn MIDI", command=learn_midi, bg="gray40", fg="white", width=12, takefocus=0).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Cancel", command=dialog.destroy, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)
    
    def _edit_midi_marker(self):
        """Edit MIDI marker closest to playhead."""
        if not self.midi_markers:
            messagebox.showwarning("Edit MIDI Marker", "No MIDI markers to edit")
            return
        
        # Find closest MIDI marker to playhead
        closest_marker = min(self.midi_markers, key=lambda m: abs(m["t"] - self.playhead_pos))
        
        if abs(closest_marker["t"] - self.playhead_pos) > 5.0:
            messagebox.showwarning("Edit MIDI Marker", "No MIDI marker found near playhead position")
            return
        
        # Create edit dialog
        dialog = tk.Toplevel(self.root)
        dialog.title("Edit MIDI Marker")
        dialog.geometry("500x300")
        dialog.configure(bg="gray20")
        dialog.transient(self.root)
        dialog.grab_set()
        
        tk.Label(dialog, text=f"Edit MIDI marker at {self._format_time(closest_marker['t'])}:", 
                bg="gray20", fg="white", font=("Arial", 10, "bold")).pack(pady=10)
        
        # Create form frame
        form_frame = tk.Frame(dialog, bg="gray20")
        form_frame.pack(pady=10, padx=20, fill=tk.BOTH)
        
        # Note
        tk.Label(form_frame, text="MIDI Note (0-127):", bg="gray20", fg="white").grid(row=0, column=0, sticky="w", pady=5)
        note_var = tk.IntVar(value=closest_marker.get("note", 60))
        note_spin = tk.Spinbox(form_frame, from_=0, to=127, textvariable=note_var, bg="gray40", fg="white", width=15)
        note_spin.grid(row=0, column=1, pady=5, padx=10)
        
        # Velocity
        tk.Label(form_frame, text="Velocity (0-127):", bg="gray20", fg="white").grid(row=1, column=0, sticky="w", pady=5)
        velocity_var = tk.IntVar(value=closest_marker.get("velocity", 100))
        velocity_spin = tk.Spinbox(form_frame, from_=0, to=127, textvariable=velocity_var, bg="gray40", fg="white", width=15)
        velocity_spin.grid(row=1, column=1, pady=5, padx=10)
        
        # Channel
        tk.Label(form_frame, text="MIDI Channel (1-16):", bg="gray20", fg="white").grid(row=2, column=0, sticky="w", pady=5)
        channel_var = tk.IntVar(value=closest_marker.get("channel", 1))
        channel_spin = tk.Spinbox(form_frame, from_=1, to=16, textvariable=channel_var, bg="gray40", fg="white", width=15)
        channel_spin.grid(row=2, column=1, pady=5, padx=10)
        
        # Duration
        tk.Label(form_frame, text="Duration (seconds):", bg="gray20", fg="white").grid(row=3, column=0, sticky="w", pady=5)
        duration_var = tk.DoubleVar(value=closest_marker.get("duration", 0.1))
        duration_spin = tk.Spinbox(form_frame, from_=0.01, to=10.0, increment=0.1, textvariable=duration_var, 
                                   bg="gray40", fg="white", width=15)
        duration_spin.grid(row=3, column=1, pady=5, padx=10)
        
        # Label
        tk.Label(form_frame, text="Label (optional):", bg="gray20", fg="white").grid(row=4, column=0, sticky="w", pady=5)
        label_var = tk.StringVar(value=closest_marker.get("label", ""))
        label_entry = tk.Entry(form_frame, textvariable=label_var, bg="gray40", fg="white", width=25)
        label_entry.grid(row=4, column=1, pady=5, padx=10)
        
        # Learn MIDI button: detect incoming MIDI and set fields (same as Add dialog)
        def learn_midi():
            try:
                if not HAS_WINDOWS_MIDI:
                    messagebox.showinfo("MIDI Learn", "Windows MIDI not available on this system.")
                    return
                # Enumerate Windows MIDI input devices using winmm
                winmm = ctypes.windll.winmm
                num_devs = winmm.midiInGetNumDevs()
                devices = []
                class MIDIINCAPS(ctypes.Structure):
                    _fields_ = [
                        ("wMid", ctypes.wintypes.WORD),
                        ("wPid", ctypes.wintypes.WORD),
                        ("vDriverVersion", ctypes.wintypes.DWORD),
                        ("szPname", ctypes.c_wchar * 32),
                        ("dwSupport", ctypes.wintypes.DWORD),
                    ]
                for i in range(num_devs):
                    caps = MIDIINCAPS()
                    res = winmm.midiInGetDevCapsW(i, ctypes.byref(caps), ctypes.sizeof(caps))
                    if res == 0:
                        devices.append(f"[{i}] {caps.szPname}")
                if not devices:
                    messagebox.showinfo("MIDI Learn", "No Windows MIDI input devices found.")
                    return

                # Selection dialog
                sel = tk.Toplevel(dialog)
                sel.title("Select Windows MIDI Input")
                sel.geometry("420x260")
                sel.configure(bg="gray20")
                tk.Label(sel, text="Select an input device to learn from:", bg="gray20", fg="white").pack(pady=8)
                in_var = tk.StringVar(value=devices[0])
                list_frame = tk.Frame(sel, bg="gray20")
                list_frame.pack(fill=tk.BOTH, expand=True)
                for nm in devices:
                    ttk.Radiobutton(list_frame, text=nm, variable=in_var, value=nm).pack(anchor="w", pady=2)

                def start_learn_winmm():
                    try:
                        dev_label = in_var.get()
                        dev_id = int(dev_label.split("]")[0].strip("["))
                        sel.destroy()

                        # Define callback type with 64-bit safe pointer sizes
                        DWORD_PTR = ctypes.c_size_t
                        CALLBACK = ctypes.WINFUNCTYPE(None, ctypes.wintypes.HANDLE, ctypes.wintypes.UINT, DWORD_PTR, DWORD_PTR, DWORD_PTR)

                        learned = {"done": False}

                        def midi_in_callback(hMidiIn, wMsg, dwInstance, dwParam1, dwParam2):
                            MIM_DATA = 0x3C3
                            try:
                                debug_log(f"LEARN: callback wMsg=0x{wMsg:X} dwParam1=0x{dwParam1:X} dwParam2=0x{dwParam2:X}")
                            except Exception:
                                pass
                            if wMsg == MIM_DATA and not learned["done"]:
                                msg = dwParam1
                                status = msg & 0xFF
                                note = (msg >> 8) & 0xFF
                                velocity = (msg >> 16) & 0xFF
                                status_type = status & 0xF0
                                channel = (status & 0x0F) + 1
                                debug_log(f"LEARN: parsed status=0x{status:02X} type=0x{status_type:02X} note={note} vel={velocity} ch={channel}")
                                def add_log():
                                    try:
                                        log_list.insert(tk.END, f"status=0x{status:02X} type=0x{status_type:02X} note={note} vel={velocity} ch={channel}")
                                        log_list.see(tk.END)
                                    except Exception:
                                        pass
                                self.root.after(0, add_log)
                                if status_type == 0x90 and velocity > 0:
                                    def apply_values():
                                        note_var.set(int(note))
                                        velocity_var.set(int(velocity))
                                        channel_var.set(int(channel))
                                        self._show_status(f"Learned note {note} ch {channel}")
                                    self.root.after(0, apply_values)
                                    learned["done"] = True
                                else:
                                    def show_info():
                                        self._show_status(f"Received MIDI status=0x{status:02X} note={note} vel={velocity}")
                                    self.root.after(0, show_info)

                        cb = CALLBACK(midi_in_callback)
                        self._midi_in_cb = cb

                        listen = tk.Toplevel(dialog)
                        listen.title("Listening for MIDI…")
                        listen.geometry("320x180")
                        listen.configure(bg="gray20")
                        tk.Label(listen, text="Play a note on your MIDI device",
                                 bg="gray20", fg="white").pack(pady=10)
                        log_frame = tk.Frame(listen, bg="gray20")
                        log_frame.pack(fill=tk.BOTH, expand=True, padx=8)
                        log_list = tk.Listbox(log_frame, height=4)
                        log_list.pack(fill=tk.BOTH, expand=True)
                        cancel_flag = {"stop": False}
                        def cancel_listen():
                            cancel_flag["stop"] = True
                            listen.destroy()
                        ttk.Button(listen, text="Cancel", command=cancel_listen).pack(pady=6)

                        hIn = ctypes.c_void_p()
                        res_open = winmm.midiInOpen(ctypes.byref(hIn), dev_id, cb, 0, 0x00030000)
                        if res_open != 0:
                            listen.destroy()
                            messagebox.showerror("MIDI Learn Failed", f"Failed to open device {dev_id}, code={res_open}")
                            return
                        debug_log(f"LEARN: opened device id={dev_id}, code={res_open}, handle={hIn}")
                        rc_start = winmm.midiInStart(hIn)
                        debug_log(f"LEARN: midiInStart rc={rc_start}")
                        self._midi_in_handle = hIn

                        def worker():
                            try:
                                deadline = time.time() + 10.0
                                while time.time() < deadline and not learned["done"] and not cancel_flag["stop"]:
                                    time.sleep(0.02)
                            finally:
                                try:
                                    rc_stop = winmm.midiInStop(hIn)
                                    rc_reset = winmm.midiInReset(hIn)
                                    rc_close = winmm.midiInClose(hIn)
                                    debug_log(f"LEARN: midiInStop rc={rc_stop}, reset rc={rc_reset}, close rc={rc_close}")
                                except Exception:
                                    pass
                                try:
                                    self._midi_in_handle = None
                                    self._midi_in_cb = None
                                except Exception:
                                    pass
                                try:
                                    self.root.after(0, listen.destroy)
                                except Exception:
                                    pass
                                if not learned["done"] and not cancel_flag["stop"]:
                                    self.root.after(0, lambda: messagebox.showinfo("MIDI Learn", "No note detected within 10 seconds."))

                        threading.Thread(target=worker, daemon=True).start()
                    except Exception as e:
                        messagebox.showerror("MIDI Learn Failed", str(e))

                ttk.Button(sel, text="Start Learn", command=start_learn_winmm).pack(pady=10)
                ttk.Button(sel, text="Cancel", command=sel.destroy).pack()
            except Exception as e:
                messagebox.showerror("MIDI Learn Error", str(e))

        def save_changes():
            try:
                self._save_undo_state()
                closest_marker["note"] = note_var.get()
                closest_marker["velocity"] = velocity_var.get()
                closest_marker["channel"] = channel_var.get()
                closest_marker["duration"] = duration_var.get()
                closest_marker["label"] = label_var.get().strip()
                self.waveform_cached = False
                self._update_canvas_view()
                dialog.destroy()
            except Exception as e:
                messagebox.showerror("Error", f"Invalid MIDI parameters: {e}")
        
        button_frame = tk.Frame(dialog, bg="gray20")
        button_frame.pack(pady=10)
        def test_current_midi():
            try:
                if not self.midi_output_port:
                    messagebox.showwarning("MIDI", "Select a MIDI output device in Settings first")
                    return
                n = int(note_var.get())
                v = int(velocity_var.get())
                ch = int(channel_var.get())
                dur = float(duration_var.get())
                self._send_midi_note(n, v, ch, max(0.01, dur))
                try:
                    self._show_status(f"Tested MIDI note {n} ch {ch}")
                except Exception:
                    pass
            except Exception as e:
                messagebox.showerror("MIDI Test Failed", str(e))

        tk.Button(button_frame, text="Save", command=save_changes, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Test MIDI", command=test_current_midi, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Learn MIDI", command=learn_midi, bg="gray40", fg="white", width=12, takefocus=0).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Cancel", command=dialog.destroy, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)

    def _add_osc_marker(self):
        """Add an OSC marker at the current playhead time."""
        dialog = tk.Toplevel(self.root)
        dialog.title("Add OSC Marker")
        dialog.geometry("520x320")
        dialog.configure(bg="gray20")
        dialog.transient(self.root)
        dialog.grab_set()

        tk.Label(dialog, text=f"OSC marker at {self._format_time(self.playhead_pos)}:",
                 bg="gray20", fg="white", font=("Arial", 10, "bold")).pack(pady=10)

        form = tk.Frame(dialog, bg="gray20")
        form.pack(pady=10, padx=20, fill=tk.BOTH)

        # Name
        tk.Label(form, text="Name:", bg="gray20", fg="white").grid(row=0, column=0, sticky="w", pady=5)
        name_var = tk.StringVar(value="OSC")
        tk.Entry(form, textvariable=name_var, bg="gray40", fg="white", width=30).grid(row=0, column=1, pady=5, padx=10)

        # IP (dropdown with recent targets)
        tk.Label(form, text="IP:", bg="gray20", fg="white").grid(row=1, column=0, sticky="w", pady=5)
        ip_var = tk.StringVar(value="127.0.0.1")
        try:
            from tkinter import ttk as _ttk
            ip_combo = _ttk.Combobox(form, textvariable=ip_var, values=getattr(self, 'recent_osc_ips', []), width=28)
            ip_combo.grid(row=1, column=1, pady=5, padx=10, sticky="w")
        except Exception:
            tk.Entry(form, textvariable=ip_var, bg="gray40", fg="white", width=30).grid(row=1, column=1, pady=5, padx=10)

        # Port
        tk.Label(form, text="Port:", bg="gray20", fg="white").grid(row=2, column=0, sticky="w", pady=5)
        port_var = tk.IntVar(value=8000)
        tk.Spinbox(form, from_=1, to=65535, textvariable=port_var, bg="gray40", fg="white", width=10).grid(row=2, column=1, sticky="w", pady=5, padx=10)

        # Address
        tk.Label(form, text="OSC Address:", bg="gray20", fg="white").grid(row=3, column=0, sticky="w", pady=5)
        addr_var = tk.StringVar(value="/")
        tk.Entry(form, textvariable=addr_var, bg="gray40", fg="white", width=30).grid(row=3, column=1, pady=5, padx=10)

        # Args
        tk.Label(form, text="Args (CSV):", bg="gray20", fg="white").grid(row=4, column=0, sticky="w", pady=5)
        args_var = tk.StringVar(value="")
        tk.Entry(form, textvariable=args_var, bg="gray40", fg="white", width=30).grid(row=4, column=1, pady=5, padx=10)

        def parse_args(text):
            vals = []
            for item in [s.strip() for s in text.split(',') if s.strip()]:
                # try int, then float, else string
                try:
                    vals.append(int(item))
                    continue
                except Exception:
                    pass
                try:
                    vals.append(float(item))
                    continue
                except Exception:
                    pass
                vals.append(item)
            return vals

        def save_osc_marker():
            try:
                name = name_var.get().strip() or "OSC"
                ip = ip_var.get().strip()
                port = int(port_var.get())
                address = addr_var.get().strip()
                if not address.startswith('/'):
                    messagebox.showerror("OSC", "Address must start with '/'")
                    return
                args = parse_args(args_var.get())
                self._save_undo_state()
                self.osc_markers.append({
                    "t": self.playhead_pos,
                    "name": name,
                    "ip": ip,
                    "port": port,
                    "address": address,
                    "args": args
                })
                # Remember IP for future quick selection
                try:
                    if not hasattr(self, 'recent_osc_ips'):
                        self.recent_osc_ips = []
                    if ip and str(ip) not in self.recent_osc_ips:
                        self.recent_osc_ips.append(str(ip))
                        # optional cap to last 20
                        if len(self.recent_osc_ips) > 20:
                            self.recent_osc_ips = self.recent_osc_ips[-20:]
                except Exception:
                    pass
                self.osc_markers.sort(key=lambda m: m["t"])
                self.waveform_cached = False
                self._update_canvas_view()
                dialog.destroy()
            except Exception as e:
                messagebox.showerror("OSC", f"Invalid parameters: {e}")

        btns = tk.Frame(dialog, bg="gray20")
        btns.pack(pady=10)
        def send_current_osc():
            try:
                ip = ip_var.get().strip()
                port = int(port_var.get())
                address = addr_var.get().strip()
                if not address.startswith('/'):
                    messagebox.showerror("OSC", "Address must start with '/'")
                    return
                args = parse_args(args_var.get())
                self._send_osc(ip, port, address, args)
                # Remember IP on quick send as well
                try:
                    if not hasattr(self, 'recent_osc_ips'):
                        self.recent_osc_ips = []
                    if ip and str(ip) not in self.recent_osc_ips:
                        self.recent_osc_ips.append(str(ip))
                        if len(self.recent_osc_ips) > 20:
                            self.recent_osc_ips = self.recent_osc_ips[-20:]
                except Exception:
                    pass
                try:
                    if not hasattr(dialog, "_osc_send_status"):
                        dialog._osc_send_status = tk.Label(btns, text="Sent ✓", bg="gray20", fg="#66bb6a", font=("Segoe UI", 9, "bold"))
                        dialog._osc_send_status.pack(side=tk.LEFT, padx=8)
                    else:
                        dialog._osc_send_status.configure(text="Sent ✓")
                    # Auto-hide after 2 seconds
                    dialog.after(2000, lambda: dialog._osc_send_status.configure(text=""))
                except Exception:
                    pass
            except Exception as e:
                messagebox.showerror("OSC", f"Send failed: {e}")
        tk.Button(btns, text="Send", command=send_current_osc, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)
        tk.Button(btns, text="Add", command=save_osc_marker, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)
        tk.Button(btns, text="Cancel", command=dialog.destroy, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)

    def _edit_osc_marker(self, idx=None):
        """Edit OSC marker closest to playhead or by index."""
        if not self.osc_markers:
            messagebox.showwarning("Edit OSC Marker", "No OSC markers to edit")
            return
        if idx is None:
            # Find closest OSC marker to playhead
            closest = min(self.osc_markers, key=lambda m: abs(float(m.get("t", 0.0)) - self.playhead_pos))
        else:
            if not (0 <= idx < len(self.osc_markers)):
                return
            closest = self.osc_markers[idx]

        dialog = tk.Toplevel(self.root)
        dialog.title("Edit OSC Marker")
        dialog.geometry("520x320")
        dialog.configure(bg="gray20")
        dialog.transient(self.root)
        dialog.grab_set()

        tk.Label(dialog, text=f"Edit OSC marker at {self._format_time(float(closest.get('t', 0.0)))}:",
                 bg="gray20", fg="white", font=("Arial", 10, "bold")).pack(pady=10)

        form = tk.Frame(dialog, bg="gray20")
        form.pack(pady=10, padx=20, fill=tk.BOTH)

        # Name
        tk.Label(form, text="Name:", bg="gray20", fg="white").grid(row=0, column=0, sticky="w", pady=5)
        name_var = tk.StringVar(value=str(closest.get("name", "OSC")))
        tk.Entry(form, textvariable=name_var, bg="gray40", fg="white", width=30).grid(row=0, column=1, pady=5, padx=10)

        # IP (dropdown with recent targets)
        tk.Label(form, text="IP:", bg="gray20", fg="white").grid(row=1, column=0, sticky="w", pady=5)
        ip_var = tk.StringVar(value=str(closest.get("ip", "127.0.0.1")))
        try:
            from tkinter import ttk as _ttk
            ip_combo = _ttk.Combobox(form, textvariable=ip_var, values=getattr(self, 'recent_osc_ips', []), width=28)
            ip_combo.grid(row=1, column=1, pady=5, padx=10, sticky="w")
        except Exception:
            tk.Entry(form, textvariable=ip_var, bg="gray40", fg="white", width=30).grid(row=1, column=1, pady=5, padx=10)

        # Port
        tk.Label(form, text="Port:", bg="gray20", fg="white").grid(row=2, column=0, sticky="w", pady=5)
        port_var = tk.IntVar(value=int(closest.get("port", 8000)))
        tk.Spinbox(form, from_=1, to=65535, textvariable=port_var, bg="gray40", fg="white", width=10).grid(row=2, column=1, sticky="w", pady=5, padx=10)

        # Address
        tk.Label(form, text="OSC Address:", bg="gray20", fg="white").grid(row=3, column=0, sticky="w", pady=5)
        addr_var = tk.StringVar(value=str(closest.get("address", "/")))
        tk.Entry(form, textvariable=addr_var, bg="gray40", fg="white", width=30).grid(row=3, column=1, pady=5, padx=10)

        # Args
        tk.Label(form, text="Args (CSV):", bg="gray20", fg="white").grid(row=4, column=0, sticky="w", pady=5)
        def _args_to_text(args):
            try:
                return ", ".join(str(a) for a in (args if isinstance(args, list) else [args]))
            except Exception:
                return ""
        args_var = tk.StringVar(value=_args_to_text(closest.get("args", [])))
        tk.Entry(form, textvariable=args_var, bg="gray40", fg="white", width=30).grid(row=4, column=1, pady=5, padx=10)

        def parse_args(text):
            vals = []
            for item in [s.strip() for s in text.split(',') if s.strip()]:
                try:
                    vals.append(int(item)); continue
                except Exception:
                    pass
                try:
                    vals.append(float(item)); continue
                except Exception:
                    pass
                vals.append(item)
            return vals

        def save_changes():
            try:
                closest["name"] = name_var.get().strip() or "OSC"
                closest["ip"] = ip_var.get().strip()
                closest["port"] = int(port_var.get())
                address = addr_var.get().strip()
                if not address.startswith('/'):
                    messagebox.showerror("OSC", "Address must start with '/'")
                    return
                closest["address"] = address
                closest["args"] = parse_args(args_var.get())
                # Remember IP for future quick selection
                try:
                    ip = closest["ip"]
                    if not hasattr(self, 'recent_osc_ips'):
                        self.recent_osc_ips = []
                    if ip and str(ip) not in self.recent_osc_ips:
                        self.recent_osc_ips.append(str(ip))
                        if len(self.recent_osc_ips) > 20:
                            self.recent_osc_ips = self.recent_osc_ips[-20:]
                except Exception:
                    pass
                self.waveform_cached = False
                self._update_canvas_view()
                dialog.destroy()
            except Exception as e:
                messagebox.showerror("OSC", f"Invalid parameters: {e}")

        btns = tk.Frame(dialog, bg="gray20")
        btns.pack(pady=10)
        def send_current_osc():
            try:
                ip = ip_var.get().strip()
                port = int(port_var.get())
                address = addr_var.get().strip()
                if not address.startswith('/'):
                    messagebox.showerror("OSC", "Address must start with '/'")
                    return
                args = parse_args(args_var.get())
                self._send_osc(ip, port, address, args)
                # Remember IP on quick send
                try:
                    if not hasattr(self, 'recent_osc_ips'):
                        self.recent_osc_ips = []
                    if ip and str(ip) not in self.recent_osc_ips:
                        self.recent_osc_ips.append(str(ip))
                        if len(self.recent_osc_ips) > 20:
                            self.recent_osc_ips = self.recent_osc_ips[-20:]
                except Exception:
                    pass
                try:
                    if not hasattr(dialog, "_osc_send_status"):
                        dialog._osc_send_status = tk.Label(btns, text="Sent ✓", bg="gray20", fg="#66bb6a", font=("Segoe UI", 9, "bold"))
                        dialog._osc_send_status.pack(side=tk.LEFT, padx=8)
                    else:
                        dialog._osc_send_status.configure(text="Sent ✓")
                    dialog.after(2000, lambda: dialog._osc_send_status.configure(text=""))
                except Exception:
                    pass
            except Exception as e:
                messagebox.showerror("OSC", f"Send failed: {e}")
        tk.Button(btns, text="Send", command=send_current_osc, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)
        tk.Button(btns, text="Save", command=save_changes, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)
        tk.Button(btns, text="Cancel", command=dialog.destroy, bg="gray40", fg="white", width=10, takefocus=0).pack(side=tk.LEFT, padx=5)
    
    def _delete_midi_marker(self):
        """Delete MIDI marker closest to playhead."""
        if not self.midi_markers:
            messagebox.showwarning("Delete MIDI Marker", "No MIDI markers to delete")
            return
        
        # Find closest MIDI marker to playhead
        closest_marker = min(self.midi_markers, key=lambda m: abs(m["t"] - self.playhead_pos))
        
        if abs(closest_marker["t"] - self.playhead_pos) > 5.0:
            messagebox.showwarning("Delete MIDI Marker", "No MIDI marker found near playhead position")
            return
        
        self._save_undo_state()
        self.midi_markers.remove(closest_marker)
        self.selected_midi_marker = None
        self.waveform_cached = False
        self._update_canvas_view()
    
    def _delete_all_midi_markers(self):
        """Delete all MIDI markers."""
        if not self.midi_markers:
            messagebox.showwarning("Delete All MIDI Markers", "No MIDI markers to delete")
            return
        
        result = messagebox.askyesno("Delete All MIDI Markers", 
                                     f"Delete all {len(self.midi_markers)} MIDI markers?")
        if result:
            self._save_undo_state()
            self.midi_markers = []
            self.selected_midi_marker = None
            self.waveform_cached = False
            self._update_canvas_view()
    
    def _open_dmx_filter(self):
        """Open DMX channel filter dialog."""
        dialog = tk.Toplevel(self.root)
        dialog.title("DMX Channel Filter")
        dialog.geometry("1000x850")
        dialog.minsize(950, 800)
        dialog.configure(bg="gray20")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Main frame
        main_frame = ttk.Frame(dialog, padding=10)
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Universe selection frame
        universe_frame = ttk.LabelFrame(main_frame, text="Capture Universes", padding=10)
        universe_frame.pack(fill=tk.X, pady=5)
        
        universe_filter_var = tk.BooleanVar(value=self.universe_filter_enabled)
        ttk.Checkbutton(universe_frame, text="Enable Universe Filter", variable=universe_filter_var).pack(anchor="w", pady=(0, 5))
        
        # Universe checkboxes in a scrollable canvas
        canvas = tk.Canvas(universe_frame, bg="gray30", height=120)
        scrollbar = ttk.Scrollbar(universe_frame, orient="vertical", command=canvas.yview)
        universe_list_frame = ttk.Frame(canvas)
        
        universe_list_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=universe_list_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        universe_vars = {}
        
        # Create checkbox for each universe in a 4-column grid
        for u in range(32):
            var = tk.BooleanVar(value=u in self.universe_filter_list)
            cb = ttk.Checkbutton(universe_list_frame, text=f"U{u}", variable=var)
            cb.grid(row=u // 4, column=u % 4, sticky="w", padx=5, pady=2)
            universe_vars[u] = var
        
        # Enable filter checkbox
        filter_var = tk.BooleanVar(value=self.dmx_filter_enabled)
        ttk.Separator(main_frame, orient="horizontal").pack(fill=tk.X, pady=10)
        enable_check = ttk.Checkbutton(main_frame, text="Enable Channel Filter", variable=filter_var)
        enable_check.pack(anchor="w", pady=(0, 10))
        
        # Quick presets frame
        preset_frame = ttk.LabelFrame(main_frame, text="Quick Presets", padding=10)
        preset_frame.pack(fill=tk.X, pady=5)
        
        def apply_preset(channels):
            self.dmx_filter_channels = list(channels)
            filter_var.set(True)
            update_listbox()
        
        ttk.Button(preset_frame, text="All Channels (0-511)", 
                   command=lambda: apply_preset(range(512))).pack(side=tk.LEFT, padx=5)
        ttk.Button(preset_frame, text="First 32", 
                   command=lambda: apply_preset(range(32))).pack(side=tk.LEFT, padx=5)
        ttk.Button(preset_frame, text="First 64", 
                   command=lambda: apply_preset(range(64))).pack(side=tk.LEFT, padx=5)
        ttk.Button(preset_frame, text="First 128", 
                   command=lambda: apply_preset(range(128))).pack(side=tk.LEFT, padx=5)
        
        # Channel range frame
        range_frame = ttk.LabelFrame(main_frame, text="Select Range", padding=10)
        range_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(range_frame, text="From Channel:").pack(side=tk.LEFT, padx=5)
        from_var = tk.IntVar(value=0)
        from_spin = ttk.Spinbox(range_frame, from_=0, to=511, textvariable=from_var, width=5)
        from_spin.pack(side=tk.LEFT, padx=5)
        
        ttk.Label(range_frame, text="To Channel:").pack(side=tk.LEFT, padx=5)
        to_var = tk.IntVar(value=511)
        to_spin = ttk.Spinbox(range_frame, from_=0, to=511, textvariable=to_var, width=5)
        to_spin.pack(side=tk.LEFT, padx=5)
        
        def apply_range():
            start = max(0, min(511, from_var.get()))
            end = max(start, min(511, to_var.get()))
            self.dmx_filter_channels = list(range(start, end + 1))
            filter_var.set(True)
            update_listbox()
        
        ttk.Button(range_frame, text="Apply Range", command=apply_range).pack(side=tk.LEFT, padx=5)
        
        # Channel list frame
        list_frame = ttk.LabelFrame(main_frame, text="Active Channels", padding=10)
        list_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        # Listbox with scrollbar
        scrollbar = ttk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        channel_listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set, bg="gray40", fg="white", height=10)
        channel_listbox.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=channel_listbox.yview)
        
        def update_listbox():
            channel_listbox.delete(0, tk.END)
            for ch in self.dmx_filter_channels:
                channel_listbox.insert(tk.END, f"Ch {ch}")
        
        update_listbox()
        
        # Button frame
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(fill=tk.X, pady=10)
        
        def save_filter():
            # Read values from UI
            universe_enabled = universe_filter_var.get()
            universe_list = [u for u in range(32) if universe_vars[u].get()]
            channel_enabled = filter_var.get()
            
            # Validate
            if universe_enabled and not universe_list:
                messagebox.showwarning("DMX Filter", "Please select at least one universe")
                return
            
            if channel_enabled and not self.dmx_filter_channels:
                messagebox.showwarning("DMX Filter", "Please select at least one channel")
                return
            
            # NOW save everything to self
            self.universe_filter_enabled = universe_enabled
            self.universe_filter_list = universe_list
            self.dmx_filter_enabled = channel_enabled

            # Sync monitored universe and UI to the new filter state
            if self.universe_filter_enabled and self.universe_filter_list:
                self.selected_universe = int(self.universe_filter_list[0])
            else:
                self.selected_universe = 1
            self.universe_var.set(str(self.selected_universe))
            
            # Also save to a config file for persistence
            try:
                import json
                config_file = "dmx_filter_config.json"
                config = {
                    "universe_filter_enabled": self.universe_filter_enabled,
                    "universe_filter_list": self.universe_filter_list,
                    "dmx_filter_enabled": self.dmx_filter_enabled,
                    "dmx_filter_channels": self.dmx_filter_channels
                }
                with open(config_file, 'w') as f:
                    json.dump(config, f)
            except Exception as e:
                print(f"Error saving config: {e}")
            
            # Update the monitor
            self._update_dmx_monitor_layout()
            # Refresh ignore status in toolbar
            try:
                self._refresh_ignore_status()
            except Exception:
                pass
            dialog.destroy()

        ttk.Label(button_frame, text="Closing this dialog saves changes. Use Cancel to discard.").pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Close (Saves)", command=save_filter).pack(side=tk.RIGHT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=dialog.destroy).pack(side=tk.RIGHT, padx=5)

        # Closing the window via the title bar also saves
        dialog.protocol("WM_DELETE_WINDOW", save_filter)

        # --- Ignore-on-Capture Section ---
        ignore_frame = ttk.LabelFrame(main_frame, text="Ignore Active Channels on Capture", padding=10)
        ignore_frame.pack(fill=tk.BOTH, expand=True, pady=10)

        ignore_enabled_var = tk.BooleanVar(value=self.ignored_on_capture_enabled)
        ttk.Checkbutton(ignore_frame, text="Enable Ignore-on-Capture", variable=ignore_enabled_var).pack(anchor="w", pady=(0,6))

        # Table to display learned channels per universe with current values
        table = ttk.Treeview(ignore_frame, columns=("universe", "channel", "value"), show="headings", height=12)
        table.heading("universe", text="Universe")
        table.heading("channel", text="Channel")
        table.heading("value", text="Current Value (baseline)")
        table.column("universe", width=90, anchor="center")
        table.column("channel", width=120, anchor="center")
        table.column("value", width=180, anchor="center")
        # Add scrollbar for the table
        table_scroll = ttk.Scrollbar(ignore_frame, orient="vertical", command=table.yview)
        table.configure(yscrollcommand=table_scroll.set)
        table.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        table_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        def refresh_table():
            try:
                for row in table.get_children():
                    table.delete(row)
                for u, chans in sorted(self.ignored_on_capture.items()):
                    if not chans:
                        continue
                    baseline = self.ignored_baseline.get(u, {})
                    for ch in sorted(chans):
                        val = int(baseline.get(ch, 0))
                        table.insert("", tk.END, values=(f"U{u}", ch, val))
            except Exception:
                pass

        def learn_active():
            try:
                # Determine universes to examine
                if self.universe_filter_enabled and self.universe_filter_list:
                    universes = list(self.universe_filter_list)
                else:
                    universes = sorted(self.dmx_values.keys())
                if not universes:
                    messagebox.showinfo("Learn", "No universes with data to learn from.")
                    return
                learned_any = False
                for u in universes:
                    values = self.dmx_values.get(u, {})
                    if not values:
                        continue
                    # Initialize structures
                    if u not in self.ignored_on_capture:
                        self.ignored_on_capture[u] = set()
                    if u not in self.ignored_baseline:
                        self.ignored_baseline[u] = {}
                    # Learn channels currently with activity (>0)
                    for ch, val in values.items():
                        if val > 0:
                            self.ignored_on_capture[u].add(ch)
                            self.ignored_baseline[u][ch] = int(val)
                            learned_any = True
                refresh_table()
                if learned_any:
                    self._show_status("Learned active channels to ignore on capture")
                    try:
                        self._refresh_ignore_status()
                    except Exception:
                        pass
                else:
                    messagebox.showinfo("Learn", "No active channels detected.")
            except Exception as e:
                messagebox.showerror("Learn Failed", str(e))

        def clear_learned():
            try:
                self.ignored_on_capture.clear()
                self.ignored_baseline.clear()
                refresh_table()
                self._show_status("Cleared learned ignore list")
                try:
                    self._refresh_ignore_status()
                except Exception:
                    pass
            except Exception as e:
                messagebox.showerror("Clear Failed", str(e))

        ctrl_row = ttk.Frame(ignore_frame)
        ctrl_row.pack(fill=tk.X, pady=6)
        ttk.Button(ctrl_row, text="Learn Active", command=learn_active).pack(side=tk.LEFT)
        ttk.Button(ctrl_row, text="Clear Learned", command=clear_learned).pack(side=tk.LEFT, padx=6)

        refresh_table()

        # Ensure changes to checkbox affect app state immediately
        def on_toggle_ignore(*_):
            try:
                self.ignored_on_capture_enabled = bool(ignore_enabled_var.get())
                try:
                    self._refresh_ignore_status()
                except Exception:
                    pass
            except Exception:
                pass
        ignore_enabled_var.trace_add("write", lambda *args: on_toggle_ignore())
    
    def _on_monitor_frame_resize(self, event):
        """Rebuild monitor layout when frame is resized to show more/fewer channels."""
        # Use event.height directly for more reliable sizing
        current_height = event.height if event.height > 0 else self.monitor_frame.winfo_height()
        
        if not hasattr(self, "_last_monitor_height"):
            self._last_monitor_height = current_height
            return  # First resize, just record the height
        
        # Rebuild if height changed by more than 30px (lower threshold for more responsiveness)
        if abs(current_height - self._last_monitor_height) > 30:
            self._last_monitor_height = current_height
            self._update_dmx_monitor_layout()
    
    def _update_dmx_monitor_layout(self):
        """Update DMX monitor grid based on filter settings and available space."""
        # Destroy old labels only
        for ch in range(512):
            if ch in self.dmx_labels:
                self.dmx_labels[ch]["frame"].destroy()
        self.dmx_labels = {}
        
        # Reuse existing canvas if available, otherwise create it
        if not hasattr(self, "_monitor_canvas"):
            # Header area above live data: logo spot
            try:
                # Always (re)build the monitor header and load a fresh, large logo
                # so resizing isn't constrained by any previously downsampled image
                if hasattr(self, "_monitor_header"):
                    try:
                        for w in self._monitor_header.winfo_children():
                            w.destroy()
                    except Exception:
                        pass
                else:
                    # Create a white header area behind the logo
                    self._monitor_header = tk.Frame(self.monitor_frame, bg="#ffffff")
                    self._monitor_header.pack(fill="x", pady=(4, 6))

                self._monitor_logo_img = None
                try:
                    candidates = [
                        os.path.join(os.path.dirname(__file__), "logo.png"),
                        os.path.join(os.path.dirname(__file__), "assets", "logo.png"),
                        os.path.join(os.path.dirname(os.path.dirname(__file__)), "logo.png"),
                    ]
                    for p in candidates:
                        if os.path.exists(p):
                            try:
                                from PIL import Image, ImageTk
                                im = Image.open(p).convert("RGBA")
                                # Resize (allow upscaling) to a larger, left-justified banner size
                                target_w, target_h = 900, 280
                                src_w, src_h = im.size
                                scale = target_h / float(src_h)
                                new_w = max(1, int(src_w * scale))
                                new_h = target_h
                                if new_w > target_w:
                                    scale = target_w / float(src_w)
                                    new_w = target_w
                                    new_h = max(1, int(src_h * scale))
                                im = im.resize((new_w, new_h), resample=Image.LANCZOS)
                                self._monitor_logo_img = ImageTk.PhotoImage(im)
                                break
                            except Exception:
                                try:
                                    img = tk.PhotoImage(file=p)
                                    self._monitor_logo_img = img
                                    break
                                except Exception:
                                    self._monitor_logo_img = None
                except Exception:
                    self._monitor_logo_img = None

                if self._monitor_logo_img is not None:
                    lbl = tk.Label(self._monitor_header, image=self._monitor_logo_img, cursor="hand2", bg="#ffffff")
                    lbl.pack(side="left", padx=8, pady=6)
                    def _open_site(event=None):
                        try:
                            import webbrowser
                            webbrowser.open("https://www.nanuvation.com")
                        except Exception:
                            pass
                    try:
                        lbl.bind("<Button-1>", _open_site)
                    except Exception:
                        pass
            except Exception:
                pass

            # Prominent timecode label under logo, above live channel monitor
            try:
                # Stable container to prevent horizontal drift when toggling edit mode
                if not hasattr(self, "monitor_timecode_container"):
                    self.monitor_timecode_container = ttk.Frame(self.monitor_frame, padding=0, style="White.TFrame")
                    self.monitor_timecode_container.pack(fill="x", padx=8, pady=(0, 8))
                if not hasattr(self, "monitor_timecode_label"):
                    self.monitor_timecode_label = tk.Label(self.monitor_timecode_container, text=self._format_time(self.playhead_pos),
                                                          bg="#ffffff", fg="#000000", font=("Segoe UI", 18, "bold"),
                                                          anchor="center", justify="center")
                    # Enable inline edit on double-click
                    try:
                        self.monitor_timecode_label.bind("<Double-Button-1>", self._begin_timecode_edit)
                    except Exception:
                        pass
                # Place/refresh the label in layout inside the stable container
                # Use center anchor to avoid text width changes pushing layout horizontally
                self.monitor_timecode_label.pack(fill="x")
                # Build activity indicators and last-message labels just below timecode
                if not hasattr(self, "monitor_activity_frame"):
                    self.monitor_activity_frame = tk.Frame(self.monitor_frame, bg="#ffffff")
                    # Left: MIDI indicator and last message
                    self.monitor_midi_col = tk.Frame(self.monitor_activity_frame, bg="#ffffff")
                    self.monitor_midi_light = tk.Label(self.monitor_midi_col, text="MIDI", width=6,
                                                       bg="#dddddd", fg="#222222", font=("Segoe UI", 9, "bold"),
                                                       relief="groove")
                    self.monitor_midi_last_label = tk.Label(self.monitor_midi_col, text="—", bg="#ffffff",
                                                            fg="#333333", font=("Segoe UI", 9))
                    self.monitor_midi_light.pack(fill="x", padx=8, pady=(0, 2))
                    self.monitor_midi_last_label.pack(fill="x", padx=8, pady=(0, 6))
                    # Right: OSC indicator and last message
                    self.monitor_osc_col = tk.Frame(self.monitor_activity_frame, bg="#ffffff")
                    self.monitor_osc_light = tk.Label(self.monitor_osc_col, text="OSC", width=6,
                                                      bg="#dddddd", fg="#222222", font=("Segoe UI", 9, "bold"),
                                                      relief="groove")
                    self.monitor_osc_last_label = tk.Label(self.monitor_osc_col, text="—", bg="#ffffff",
                                                           fg="#333333", font=("Segoe UI", 9))
                    self.monitor_osc_light.pack(fill="x", padx=8, pady=(0, 2))
                    self.monitor_osc_last_label.pack(fill="x", padx=8, pady=(0, 6))
                    # Layout the two columns side-by-side
                    self.monitor_midi_col.pack(side="left", fill="x", expand=True)
                    self.monitor_osc_col.pack(side="left", fill="x", expand=True)
                    self.monitor_activity_frame.pack(fill="x")
            except Exception:
                pass

            # Header above the live channel monitor
            try:
                if not hasattr(self, "monitor_channels_header"):
                    self.monitor_channels_header = tk.Label(
                        self.monitor_frame,
                        text="Real-time Artnet Channel Monitoring:",
                        bg="#ffffff",
                        fg="#000000",
                        font=("Segoe UI", 10, "bold")
                    )
                self.monitor_channels_header.pack(fill="x", padx=8, pady=(0, 6))
            except Exception:
                pass

            # Controls row under the header: Universe, Speed, Target IP
            try:
                if not hasattr(self, "monitor_controls_frame"):
                    self.monitor_controls_frame = ttk.Frame(self.monitor_frame, padding=6, style="White.TFrame")
                    # Universe
                    ttk.Label(self.monitor_controls_frame, text="Universe:").pack(side=tk.LEFT, padx=(4, 2))
                    ttk.Spinbox(self.monitor_controls_frame, from_=0, to=15, textvariable=self.universe_var, width=4,
                                command=self._update_universe).pack(side=tk.LEFT, padx=2)
                    # Speed
                    ttk.Label(self.monitor_controls_frame, text="Speed:").pack(side=tk.LEFT, padx=(12, 2))
                    ttk.Spinbox(self.monitor_controls_frame, from_=0.1, to=4.0, textvariable=self.speed_var, width=5).pack(side=tk.LEFT, padx=2)
                    # Target IP
                    ttk.Label(self.monitor_controls_frame, text="Target IP:").pack(side=tk.LEFT, padx=(12, 2))
                    ttk.Entry(self.monitor_controls_frame, textvariable=self.target_var, width=16).pack(side=tk.LEFT, padx=2)
                self.monitor_controls_frame.pack(fill="x", padx=8, pady=(0, 6))
            except Exception:
                pass

            canvas = tk.Canvas(self.monitor_frame, bg="#ffffff", highlightthickness=0, bd=0)
            scrollbar = ttk.Scrollbar(self.monitor_frame, orient="vertical", command=canvas.yview)
            self.monitor_scroll_frame = ttk.Frame(canvas, padding=5, style="White.TFrame")
            
            self.monitor_scroll_frame.bind(
                "<Configure>",
                lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
            )
            
            self._monitor_inner_window = canvas.create_window((0, 0), window=self.monitor_scroll_frame, anchor="nw")
            canvas.configure(yscrollcommand=scrollbar.set)
            
            canvas.pack(side="left", fill="both", expand=True)
            scrollbar.pack(side="right", fill="y")
            
            self._monitor_canvas = canvas
            self._monitor_scrollbar = scrollbar
        else:
            canvas = self._monitor_canvas
            # Clear old widgets from the frame
            for widget in self.monitor_scroll_frame.winfo_children():
                widget.destroy()
        
        # Reset canvas scroll position
        canvas.xview_moveto(0)
        
        # Get channels to display: if filter is enabled, show filtered channels; otherwise show all 512 with scrolling
        if self.dmx_filter_enabled and self.dmx_filter_channels:
            channels_to_show = self.dmx_filter_channels
        else:
            channels_to_show = range(512)
        
        # Create labels for each channel in a responsive grid
        # Derive columns from available width to avoid wasted space
        # Use a strict fixed column count to avoid auto-scaling issues
        cols = 10

        # Configure columns for even stretching
        
        for c in range(cols):
            self.monitor_scroll_frame.grid_columnconfigure(c, weight=1)

        # Build grid items
        # Determine dynamic bar width to better use horizontal space
        bar_w = 40
        try:
            if avail_width and cols:
                # subtract padding/margins to get usable width per column
                per_col = max(50, int((avail_width - 16) / cols) - 12)
                bar_w = max(40, min(120, per_col - 12))
        except Exception:
            pass

        for idx, ch in enumerate(channels_to_show):
            row = idx // cols
            col = idx % cols
            
            frame = ttk.Frame(self.monitor_scroll_frame)
            frame.grid(row=row, column=col, padx=2, pady=2, sticky="nsew")
            
            # Channel label
            ttk.Label(frame, text=f"Ch{ch}", font=("mono", 8)).pack()
            
            # Value and bar
            value_label = ttk.Label(frame, text="000", foreground="gray50", font=("mono", 9, "bold"))
            value_label.pack()
            
            bar = tk.Canvas(frame, bg="gray30", width=bar_w, height=8, highlightthickness=0)
            bar.pack(pady=2)
            
            self.dmx_labels[ch] = {"value": value_label, "bar": bar, "frame": frame}

        # Enable mouse wheel scrolling on the monitor canvas
        def _on_mousewheel(event):
            try:
                delta = -1 if event.delta > 0 else 1
                self._monitor_canvas.yview_scroll(delta, "units")
            except Exception:
                pass
        try:
            self._monitor_canvas.bind_all("<MouseWheel>", _on_mousewheel)
        except Exception:
            pass
    
    def _get_windows_midi_devices(self):
        """Get list of Windows MIDI output devices using native API."""
        if not HAS_WINDOWS_MIDI:
            return []
        
        try:
            winmm = ctypes.windll.winmm
            num_devs = winmm.midiOutGetNumDevs()
            devices = []
            
            for i in range(num_devs):
                # MIDIOUTCAPS structure
                class MIDIOUTCAPS(ctypes.Structure):
                    _fields_ = [
                        ("wMid", ctypes.wintypes.WORD),
                        ("wPid", ctypes.wintypes.WORD),
                        ("vDriverVersion", ctypes.wintypes.DWORD),
                        ("szPname", ctypes.c_wchar * 32),
                        ("wTechnology", ctypes.wintypes.WORD),
                        ("wVoices", ctypes.wintypes.WORD),
                        ("wNotes", ctypes.wintypes.WORD),
                        ("wChannelMask", ctypes.wintypes.WORD),
                        ("dwSupport", ctypes.wintypes.DWORD),
                    ]
                
                caps = MIDIOUTCAPS()
                result = winmm.midiOutGetDevCapsW(i, ctypes.byref(caps), ctypes.sizeof(caps))
                if result == 0:  # MMSYSERR_NOERROR
                    devices.append(f"[{i}] {caps.szPname}")
            
            return devices
        except Exception as e:
            print(f"Error getting Windows MIDI devices: {e}")
            return []
    
    def _load_settings(self):
        """Load settings from file."""
        try:
            import json
            if os.path.exists(self.settings_file):
                with open(self.settings_file, 'r') as f:
                    return json.load(f)
        except:
            pass
        return {}
    
    def _save_settings(self):
        """Save settings to file."""
        try:
            import json
            with open(self.settings_file, 'w') as f:
                json.dump(self.settings, f, indent=2)
        except:
            pass
    
    def _send_midi_note(self, note, velocity, channel, duration):
        """Send MIDI note on/off messages."""
        if not self.has_midi or not self.midi_output_port:
            debug_log(f"DEBUG: MIDI not available or port not set (has_midi={self.has_midi}, port={self.midi_output_port})")
            return
        
        # Use Windows native MIDI when available and selected port is Windows-style
        if HAS_WINDOWS_MIDI and isinstance(self.midi_output_port, str) and self.midi_output_port.strip().startswith("["):
            debug_log("DEBUG: Routing to Windows MIDI backend")
            # Flash activity and send
            try:
                self._last_midi_note_text = f"Note {note} Ch {channel} Vel {velocity}"
            except Exception:
                pass
            self._flash_midi_activity()
            self._send_windows_midi_note(note, velocity, channel, duration)
            return
        # Otherwise, try mido backend
        if HAS_MIDI_MIDO:
            try:
                self._last_midi_note_text = f"Note {note} Ch {channel} Vel {velocity}"
            except Exception:
                pass
            self._flash_midi_activity()
            try:
                self._send_mido_note(note, velocity, channel, duration)
                return
            except Exception as e:
                debug_log(f"MIDO send error: {e}")
                return
        debug_log("DEBUG: No suitable MIDI backend available")

    def _get_osc_client(self, ip: str, port: int):
        key = (ip, int(port))
        cli = self._osc_clients.get(key)
        if cli is not None:
            return cli
        try:
            from pythonosc.udp_client import SimpleUDPClient
            cli = SimpleUDPClient(ip, int(port))
            self._osc_clients[key] = cli
            return cli
        except Exception as e:
            try:
                debug_log(f"ERROR: python-osc client unavailable: {e}")
            except Exception:
                pass
            return None

    def _get_osc_socket(self, ip: str, port: int):
        """Get or create a UDP socket bound to the configured OSC interface for a target."""
        key = (self.osc_network_interface if hasattr(self, 'osc_network_interface') else '0.0.0.0', ip, int(port))
        sock = self._osc_sockets.get(key)
        if sock:
            return sock
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            # Bind to selected interface (0.0.0.0 for any)
            try:
                s.bind((key[0], 0))
            except Exception:
                # Fallback to default
                pass
            self._osc_sockets[key] = s
            return s
        except Exception:
            return None

    def _send_osc(self, ip: str, port: int, address: str, args: list):
        # Normalize args and build display message
        payload = args if isinstance(args, list) else ([args] if args is not None else [])
        arg_text = " ".join(str(a) for a in payload) if payload else ""
        msg_text = f"{address} {arg_text}".strip()
        # Always flash indicator and update last message on main thread
        try:
            self.root.after(0, lambda: self._flash_osc_activity(msg_text))
        except Exception:
            pass
        # Attempt to send via socket bound to selected interface; build OSC datagram manually if python-osc is missing
        def _encode_osc(address_str: str, values: list) -> bytes:
            # Minimal OSC encoder: address + type tag string + arguments, all 4-byte padded
            def _pad(b: bytes) -> bytes:
                pad = (4 - (len(b) % 4)) % 4
                return b + (b"\x00" * pad)
            # address
            addr_b = _pad(address_str.encode('ascii') + b"\x00")
            # build typetags and args
            tags = ','
            arg_bytes = b''
            import struct
            for v in values:
                if isinstance(v, bool):
                    # no native bool in OSC, map to int
                    tags += 'i'; arg_bytes += struct.pack('>i', 1 if v else 0)
                elif isinstance(v, int):
                    tags += 'i'; arg_bytes += struct.pack('>i', int(v))
                elif isinstance(v, float):
                    tags += 'f'; arg_bytes += struct.pack('>f', float(v))
                elif isinstance(v, (bytes, bytearray)):
                    tags += 'b'; arg_bytes += _pad(bytes(v))
                else:
                    s = str(v)
                    tags += 's'; arg_bytes += _pad(s.encode('utf-8') + b"\x00")
            tag_b = _pad(tags.encode('ascii') + b"\x00")
            return addr_b + tag_b + arg_bytes
        try:
            sock = self._get_osc_socket(ip, port)
            if sock:
                try:
                    # Try python-osc for robustness; fall back to manual encoding
                    try:
                        from pythonosc.osc_message_builder import OscMessageBuilder
                        b = OscMessageBuilder(address=address)
                        for a in payload:
                            b.add_arg(a)
                        data = b.build().dgram
                    except Exception:
                        data = _encode_osc(address, payload)
                    sock.sendto(data, (ip, int(port)))
                    debug_log(f"DEBUG: OSC sent via socket {getattr(self,'osc_network_interface','0.0.0.0')} -> {ip}:{port} {address} {payload}")
                    return
                except Exception as e:
                    debug_log(f"ERROR: OSC socket send failed: {e}")
        except Exception:
            pass
        # Fallback to python-osc client
        try:
            cli = self._get_osc_client(ip, port)
            if cli:
                cli.send_message(address, payload)
                debug_log(f"DEBUG: OSC sent via client {ip}:{port} {address} {payload}")
        except Exception as e:
            try:
                debug_log(f"ERROR: OSC send error to {ip}:{port} {address} {args}: {e}")
            except Exception:
                pass
    
    def _send_windows_midi_note(self, note, velocity, channel, duration):
        """Send MIDI note using Windows native API."""
        try:
            # Extract device ID from port name "[0] Device Name"
            device_id = int(self.midi_output_port.split("]")[0].strip("["))
            debug_log(f"DEBUG: Windows MIDI device_id={device_id} from '{self.midi_output_port}'")
            
            winmm = ctypes.windll.winmm
            
            # If a handle exists but for a different device, close it
            try:
                if self.windows_midi_handle is not None:
                    # No direct way to query device id from handle; conservatively reset on port change
                    # Close existing handle to avoid stale device state
                    winmm.midiOutReset(self.windows_midi_handle)
                    winmm.midiOutClose(self.windows_midi_handle)
                    self.windows_midi_handle = None
                    debug_log("DEBUG: Closed previous Windows MIDI handle")
            except Exception as e:
                debug_log(f"DEBUG: Error closing previous MIDI handle: {e}")

            # Open device if not already open
            if self.windows_midi_handle is None:
                handle = ctypes.c_void_p()
                result = winmm.midiOutOpen(ctypes.byref(handle), device_id, 0, 0, 0)
                if result != 0:
                    debug_log(f"ERROR: Failed to open Windows MIDI device {device_id}, code={result}")
                    return
                self.windows_midi_handle = handle
                debug_log(f"DEBUG: Windows MIDI opened, handle={handle}")
            
            # Create MIDI note on message
            status = 0x90 + (channel - 1)  # note on
            msg_on = status | (note << 8) | (velocity << 16)
            rc = winmm.midiOutShortMsg(self.windows_midi_handle, msg_on)
            debug_log(f"DEBUG: midiOutShortMsg(note_on) rc={rc}")
            if rc == 0:
                self._show_status(f"MIDI note_on {note} ch {channel} via Windows")
            
            # Schedule note off
            def send_note_off():
                try:
                    if self.windows_midi_handle:
                        status_off = 0x80 + (channel - 1)  # note off
                        msg_off = status_off | (note << 8) | (0 << 16)
                        rc2 = winmm.midiOutShortMsg(self.windows_midi_handle, msg_off)
                        debug_log(f"DEBUG: midiOutShortMsg(note_off) rc={rc2}")
                except:
                    pass
            
            timer = threading.Timer(duration, send_note_off)
            timer.daemon = True
            timer.start()
        except Exception as e:
            debug_log(f"Windows MIDI send error: {e}")

    def _get_mido_midi_devices(self):
        """List MIDI outputs via mido (CoreMIDI on macOS)."""
        if not HAS_MIDI_MIDO:
            return []
        try:
            return list(mido.get_output_names())
        except Exception as e:
            debug_log(f"MIDO list error: {e}")
            return []

    def _send_mido_note(self, note, velocity, channel, duration):
        """Send a MIDI note via mido to the selected output port."""
        if not HAS_MIDI_MIDO or not self.midi_output_port or self.midi_output_port == "None":
            return
        try:
            # mido uses 0-based channels
            ch = max(0, int(channel) - 1)
        except Exception:
            ch = 0
        try:
            port_name = str(self.midi_output_port)
            out = mido.open_output(port_name)
        except Exception as e:
            raise RuntimeError(f"open_output failed for '{self.midi_output_port}': {e}")
        try:
            on = mido.Message('note_on', note=int(note), velocity=int(velocity), channel=ch)
            out.send(on)
            self._show_status(f"MIDI note_on {note} ch {channel} via mido")
        except Exception as e:
            try:
                out.close()
            except Exception:
                pass
            raise
        # Schedule note off
        def _note_off():
            try:
                off = mido.Message('note_off', note=int(note), velocity=0, channel=ch)
                out.send(off)
            except Exception:
                pass
            try:
                out.close()
            except Exception:
                pass
        t = threading.Timer(float(duration), _note_off)
        t.daemon = True
        t.start()
    
    def _on_exit(self):
        """Clean up and exit application."""
        # Close MIDI port if open
        if self.midi_port:
            try:
                self.midi_port.close()
            except:
                pass
        
        # Close Windows MIDI handle if open
        if hasattr(self, 'windows_midi_handle') and self.windows_midi_handle:
            try:
                winmm = ctypes.windll.winmm
                winmm.midiOutClose(self.windows_midi_handle)
            except:
                pass
        
        # Log app exit
        try:
            debug_log("APP EXIT: Timeline GUI closing")
            ts = __import__("datetime").datetime.now().astimezone().isoformat()
            line = f"{ts} APP EXIT\n"
            try:
                with open(_VERBOSE_FILE, "a", encoding="utf-8", errors="replace") as df:
                    df.write(line)
            except Exception:
                pass
        except Exception:
            pass
        self.root.quit()
    
    def _open_settings(self):
        """Open settings window."""
        import socket
        import sounddevice as sd
        
        settings_win = tk.Toplevel(self.root)
        settings_win.title("Settings - Network, Audio & MIDI")
        # Allow resizing to avoid controls being cut off
        settings_win.resizable(True, True)
        
        # Main container with three columns
        main_frame = ttk.Frame(settings_win, padding=10)
        main_frame.pack(fill=tk.BOTH, expand=True)
        try:
            # Improve grid expansion so rows/columns grow with window
            main_frame.columnconfigure(0, weight=1)
            main_frame.columnconfigure(1, weight=1)
            main_frame.columnconfigure(2, weight=1)
            main_frame.rowconfigure(0, weight=1)
            main_frame.rowconfigure(1, weight=1)
        except Exception:
            pass
        
        # Left column - Artnet Network Interface
        left_frame = ttk.LabelFrame(main_frame, text="Artnet Network Interface", padding=10)
        left_frame.grid(row=0, column=0, padx=5, pady=5, sticky="nsew")
        
        try:
            # Get all network interfaces
            interfaces = socket.gethostbyname_ex(socket.gethostname())[2]
            interfaces = list(set(["0.0.0.0"] + interfaces))
        except:
            interfaces = ["0.0.0.0"]
        
        network_var = tk.StringVar(value=self.network_interface)
        
        for intf in interfaces:
            ttk.Radiobutton(left_frame, text=intf, variable=network_var, value=intf).pack(anchor="w", pady=4)
        
        # Middle column - Audio Device
        middle_frame = ttk.LabelFrame(main_frame, text="Audio Output Device", padding=10)
        middle_frame.grid(row=0, column=1, padx=5, pady=5, sticky="nsew")
        
        try:
            devices = sd.query_devices()
            device_names = []
            for i, device in enumerate(devices):
                if device['max_output_channels'] > 0:  # Only output devices
                    device_names.append((i, device['name']))
        except:
            device_names = [(None, "Default")]
        
        audio_var = tk.StringVar(value=str(self.audio_device) if self.audio_device is not None else "None")
        
        ttk.Radiobutton(middle_frame, text="Default", variable=audio_var, value="None").pack(anchor="w", pady=4)
        
        # Create scrollable area for audio devices if there are many
        if len(device_names) > 5:
            device_canvas = tk.Canvas(middle_frame, bg="white", highlightthickness=0, height=200)
            device_scrollbar = ttk.Scrollbar(middle_frame, orient="vertical", command=device_canvas.yview)
            device_frame = ttk.Frame(device_canvas)
            
            device_frame.bind(
                "<Configure>",
                lambda e: device_canvas.configure(scrollregion=device_canvas.bbox("all"))
            )
            
            device_canvas.create_window((0, 0), window=device_frame, anchor="nw")
            device_canvas.configure(yscrollcommand=device_scrollbar.set)
            
            device_canvas.pack(side="left", fill="both", expand=True, pady=5)
            device_scrollbar.pack(side="right", fill="y")
            
            for dev_id, dev_name in device_names:
                ttk.Radiobutton(device_frame, text=dev_name, variable=audio_var, value=str(dev_id)).pack(anchor="w", pady=2)
        else:
            for dev_id, dev_name in device_names:
                ttk.Radiobutton(middle_frame, text=dev_name, variable=audio_var, value=str(dev_id)).pack(anchor="w", pady=4)
        
        # Right column - MIDI Output Device
        right_frame = ttk.LabelFrame(main_frame, text="MIDI Output Device", padding=10)
        right_frame.grid(row=0, column=2, padx=5, pady=5, sticky="nsew")
        
        midi_error = None
        midi_outputs = []
        
        # Show current status at top
        status_frame = tk.Frame(right_frame, bg="lightyellow", relief=tk.SOLID, bd=1)
        status_frame.pack(fill=tk.X, pady=(0, 10), padx=2)
        
        # Try Windows native MIDI first, then mido
        print(f"DEBUG: HAS_WINDOWS_MIDI = {HAS_WINDOWS_MIDI}, HAS_MIDI_MIDO = {HAS_MIDI_MIDO}")
        if HAS_WINDOWS_MIDI:
            try:
                midi_outputs = self._get_windows_midi_devices()
                print(f"DEBUG: Windows MIDI devices found: {midi_outputs}")
                if len(midi_outputs) > 0:
                    status_text = f"✓ Found {len(midi_outputs)} MIDI device(s) (Windows)"
                    status_color = "green"
                else:
                    status_text = "✓ Windows MIDI ready (no devices connected)"
                    status_color = "orange"
            except Exception as e:
                midi_error = str(e)
                print(f"DEBUG: Windows MIDI error: {e}")
                status_text = "✗ Windows MIDI error"
                status_color = "red"
        elif HAS_MIDI_MIDO:
            try:
                midi_outputs = self._get_mido_midi_devices()
                if len(midi_outputs) > 0:
                    status_text = f"✓ Found {len(midi_outputs)} MIDI device(s) (mido)"
                    status_color = "green"
                else:
                    status_text = "✓ mido ready (no devices connected)"
                    status_color = "orange"
            except Exception as e:
                midi_error = str(e)
                status_text = "✗ mido MIDI error"
                status_color = "red"
        else:
            status_text = "✗ MIDI not available"
            status_color = "red"
        
        ttk.Label(status_frame, text=status_text, foreground=status_color, font=("Arial", 9, "bold")).pack(pady=5)
        
        # Debug output
        print(f"Settings Dialog - has_midi: {self.has_midi}, midi_error: {midi_error}, midi_outputs: {len(midi_outputs)}")
        print(f"MIDI device list: {midi_outputs}")
        
        # Show detected devices or instructions
        if not self.has_midi:
            ttk.Label(right_frame, text="Install MIDI support:", foreground="gray").pack(anchor="w", pady=2)
            if sys.platform == "darwin":
                ttk.Label(right_frame, text="pip install mido python-rtmidi", foreground="blue", font=("Courier", 8)).pack(anchor="w", padx=10, pady=2)
            else:
                ttk.Label(right_frame, text="pip install mido", foreground="blue", font=("Courier", 8)).pack(anchor="w", padx=10, pady=2)
        elif midi_error and "rtmidi" in midi_error:
            ttk.Label(right_frame, text="MIDI Backend Required:", foreground="red", font=("Arial", 9, "bold")).pack(anchor="w", pady=5)
            ttk.Label(right_frame, text="Option 1: Install loopMIDI", foreground="gray").pack(anchor="w", pady=2)
            ttk.Label(right_frame, text="(Virtual MIDI port, no compiler)", foreground="gray", font=("Arial", 7)).pack(anchor="w", padx=10)
            ttk.Label(right_frame, text="Option 2: Install python-rtmidi", foreground="gray").pack(anchor="w", pady=(5,2))
            ttk.Label(right_frame, text="(Requires C++ Build Tools)", foreground="gray", font=("Arial", 7)).pack(anchor="w", padx=10)
        elif len(midi_outputs) == 0:
            ttk.Label(right_frame, text="No MIDI Devices Connected", foreground="orange", font=("Arial", 9, "bold")).pack(anchor="w", pady=5)
            ttk.Label(right_frame, text="• Connect a USB MIDI device", foreground="gray").pack(anchor="w", pady=2)
            ttk.Label(right_frame, text="• Install loopMIDI for virtual port", foreground="gray").pack(anchor="w", pady=2)
            ttk.Label(right_frame, text="• Restart this app after connecting", foreground="gray").pack(anchor="w", pady=2)
        else:
            ttk.Label(right_frame, text="Select MIDI Output:", font=("Arial", 9, "bold")).pack(anchor="w", pady=(5, 5))
        
        # MIDI device selection
        midi_var = tk.StringVar(value=self.midi_output_port if self.midi_output_port else "None")
        
        if len(midi_outputs) > 0:
            for port_name in midi_outputs:
                ttk.Radiobutton(right_frame, text=port_name, variable=midi_var, value=port_name).pack(anchor="w", pady=3, padx=10)
            ttk.Radiobutton(right_frame, text="Disable MIDI Output", variable=midi_var, value="None").pack(anchor="w", pady=(10, 3), padx=10)
        
        # Bottom buttons frame
        button_frame = ttk.Frame(settings_win, padding=10)
        button_frame.pack(fill=tk.X)

        # Test MIDI button (Windows native only)
        def test_midi():
            try:
                port = midi_var.get()
                if not port or port == "None":
                    messagebox.showwarning("MIDI", "Select a MIDI output device first")
                    return
                # Temporarily use selected port and send a short test note
                prev_port = self.midi_output_port
                self.midi_output_port = port
                note = self.last_test_midi_note
                channel = self.last_test_midi_channel
                if HAS_WINDOWS_MIDI and port.strip().startswith("["):
                    self._send_windows_midi_note(note=note, velocity=110, channel=channel, duration=0.2)
                elif HAS_MIDI_MIDO:
                    self._send_mido_note(note=note, velocity=110, channel=channel, duration=0.2)
                else:
                    messagebox.showwarning("MIDI", "No MIDI backend available")
                # Persist last used
                self.settings["last_test_midi_note"] = note
                self.settings["last_test_midi_channel"] = channel
                self._save_settings()
                self.midi_output_port = prev_port
                self._show_status(f"Sent test MIDI to {port}")
            except Exception as e:
                messagebox.showerror("MIDI Test Failed", str(e))
        ttk.Button(button_frame, text="Test MIDI", command=test_midi).pack(side=tk.LEFT)

        # Test All (enumerate Windows MIDI devices and send)
        def test_midi_all():
            try:
                devices = []
                if HAS_WINDOWS_MIDI:
                    devices = self._get_windows_midi_devices()
                elif HAS_MIDI_MIDO:
                    devices = self._get_mido_midi_devices()
                if not devices:
                    messagebox.showwarning("MIDI", "No Windows MIDI devices found")
                    return
                prev_port = self.midi_output_port
                for dev in devices:
                    try:
                        self.midi_output_port = dev
                        debug_log(f"DEBUG: TestAll sending to {dev}")
                        if HAS_WINDOWS_MIDI and str(dev).strip().startswith("["):
                            self._send_windows_midi_note(note=60, velocity=110, channel=1, duration=0.2)
                        elif HAS_MIDI_MIDO:
                            self._send_mido_note(note=60, velocity=110, channel=1, duration=0.2)
                    except Exception as e:
                        debug_log(f"DEBUG: TestAll error for {dev}: {e}")
                self.midi_output_port = prev_port
                self._show_status("Sent test MIDI to all Windows devices")
            except Exception as e:
                messagebox.showerror("MIDI Test Failed", str(e))
        ttk.Button(button_frame, text="Test All MIDI", command=test_midi_all).pack(side=tk.LEFT, padx=6)

        # Quick controls to set last-used test note/channel
        controls = ttk.Frame(settings_win, padding=10)
        controls.pack(fill=tk.X)
        ttk.Label(controls, text="Test Note:").pack(side=tk.LEFT)
        test_note_var = tk.IntVar(value=self.last_test_midi_note)
        ttk.Spinbox(controls, from_=0, to=127, textvariable=test_note_var, width=6).pack(side=tk.LEFT, padx=4)
        ttk.Label(controls, text="Channel:").pack(side=tk.LEFT, padx=(10,0))
        test_chan_var = tk.IntVar(value=self.last_test_midi_channel)
        ttk.Spinbox(controls, from_=1, to=16, textvariable=test_chan_var, width=6).pack(side=tk.LEFT, padx=4)
        def save_test_params():
            try:
                self.last_test_midi_note = int(test_note_var.get())
                self.last_test_midi_channel = int(test_chan_var.get())
                self.settings["last_test_midi_note"] = self.last_test_midi_note
                self.settings["last_test_midi_channel"] = self.last_test_midi_channel
                self._save_settings()
                self._show_status("Saved test MIDI params")
            except Exception as e:
                messagebox.showerror("Save Failed", str(e))
        ttk.Button(controls, text="Save Test Params", command=save_test_params).pack(side=tk.LEFT, padx=10)
        
        # OSC Network Interface
        osc_frame = ttk.LabelFrame(main_frame, text="OSC Network Interface", padding=10)
        osc_frame.grid(row=1, column=0, columnspan=3, padx=5, pady=5, sticky="nsew")
        try:
            osc_interfaces = socket.gethostbyname_ex(socket.gethostname())[2]
            osc_interfaces = list(set(["0.0.0.0"] + osc_interfaces))
        except Exception:
            osc_interfaces = ["0.0.0.0"]
        if not hasattr(self, "osc_network_interface"):
            self.osc_network_interface = self.settings.get("osc_network_interface", "0.0.0.0")
        osc_net_var = tk.StringVar(value=self.osc_network_interface)
        for intf in osc_interfaces:
            ttk.Radiobutton(osc_frame, text=intf, variable=osc_net_var, value=intf).pack(anchor="w", pady=4)

        # Save button
        def save_settings():
            self.network_interface = network_var.get()
            self.osc_network_interface = osc_net_var.get()
            audio_val = audio_var.get()
            self.audio_device = None if audio_val == "None" else int(audio_val)
            
            midi_val = midi_var.get()
            self.midi_output_port = None if midi_val == "None" else midi_val
            
            # Close existing MIDI port if open
            if self.midi_port:
                try:
                    self.midi_port.close()
                except:
                    pass
                self.midi_port = None
            
            # Log changes to key settings
            try:
                debug_log(f"SETTINGS: network_interface={self.network_interface}")
                debug_log(f"SETTINGS: osc_network_interface={self.osc_network_interface}")
                debug_log(f"SETTINGS: audio_device={self.audio_device}")
                debug_log(f"SETTINGS: midi_output_port={self.midi_output_port}")
            except Exception:
                pass
            self.settings["network_interface"] = self.network_interface
            self.settings["osc_network_interface"] = self.osc_network_interface
            self.settings["audio_device"] = self.audio_device
            self.settings["midi_output_port"] = self.midi_output_port
            self._save_settings()
            # Restart DMX monitor to apply new interface
            self._restart_dmx_monitor()
            
            messagebox.showinfo("Settings", "Settings saved successfully")
            settings_win.destroy()
        
        ttk.Button(button_frame, text="Save Settings", command=save_settings).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Close", command=settings_win.destroy).pack(side=tk.LEFT, padx=5)
        
        # Set window size for three columns
        # Increase default size to accommodate more adapters and controls
        settings_win.geometry("1100x600")
    
    def _setup_ui(self):
        """Build the main UI with menu bar, timeline canvas, controls, and monitor."""
        # Use white backgrounds across panes
        try:
            self.style = ttk.Style()
            self.style.configure("White.TFrame", background="#ffffff")
            self.style.configure("White.TLabelframe", background="#ffffff")
            self.style.configure("White.TLabelframe.Label", background="#ffffff")
        except Exception:
            pass
        # Menu bar
        menu_bar = tk.Menu(self.root)
        self.root.config(menu=menu_bar)
        
        file_menu = tk.Menu(menu_bar, tearoff=0)
        menu_bar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="New Timeline", command=self._new_timeline)
        file_menu.add_command(label="Open Timeline", command=self._open_timeline)
        file_menu.add_command(label="Save Timeline", command=self._save_timeline)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self._on_exit)
        
        record_menu = tk.Menu(menu_bar, tearoff=0)
        record_menu.add_command(label="Start Recording Artnet", command=self._start_recording, accelerator="A")
        record_menu.add_command(label="Stop Recording Artnet", command=self._stop_recording)
        # Bind keyboard shortcut for starting Art-Net recording
        try:
            self.root.bind("<a>", lambda e: self._start_recording())
        except Exception:
            pass
        
        settings_menu = tk.Menu(menu_bar, tearoff=0)
        settings_menu.add_command(label="Timeline Preferences", command=self._open_settings)
        
        edit_menu = tk.Menu(menu_bar, tearoff=0)
        edit_menu.add_command(label="Undo", command=self._undo, accelerator="Ctrl+Z")
        edit_menu.add_command(label="Redo", command=self._redo, accelerator="Ctrl+Y")
        edit_menu.add_separator()
        edit_menu.add_command(label="Rename Session", command=self._rename_session)
        edit_menu.add_command(label="Add Marker", command=self._add_marker)
        edit_menu.add_command(label="Delete Marker", command=self._delete_marker)
        edit_menu.add_separator()
        edit_menu.add_command(label="Add MIDI Marker", command=self._add_midi_marker, accelerator="M")
        edit_menu.add_command(label="Add OSC Marker", command=self._add_osc_marker, accelerator="O")
        edit_menu.add_command(label="Edit MIDI Marker", command=self._edit_midi_marker)
        edit_menu.add_command(label="Delete MIDI Marker", command=self._delete_midi_marker)
        edit_menu.add_command(label="Delete All MIDI Markers", command=self._delete_all_midi_markers)
        edit_menu.add_separator()
        edit_menu.add_command(label="Edit Session Priorities", command=self._edit_session_priorities)
        self.root.bind("<Control-z>", lambda e: self._undo())
        self.root.bind("<Control-y>", lambda e: self._redo())
        # Bind 'm' to add MIDI marker; remove conflicting plain marker hotkey
        self.root.bind("<m>", lambda e: self._add_midi_marker())
        
        playback_menu = tk.Menu(menu_bar, tearoff=0)
        playback_menu.add_command(label="Set Loop In Point", command=self._set_loop_in, accelerator="Ctrl+I")
        playback_menu.add_command(label="Set Loop Out Point", command=self._set_loop_out, accelerator="Ctrl+O")
        playback_menu.add_command(label="Toggle Loop", command=self._toggle_loop, accelerator="L")
        playback_menu.add_command(label="Clear Loop", command=self._clear_loop)
        def _kb_in_dialog_or_text():
            try:
                w = self.root.focus_get()
                if w is not None:
                    try:
                        if w.winfo_toplevel() is not self.root:
                            return True
                    except Exception:
                        pass
                    cls = str(getattr(w, 'winfo_class', lambda: '')())
                    if cls in ("Entry", "TEntry", "Text", "Spinbox", "TSpinbox", "Combobox", "TCombobox"):
                        return True
            except Exception:
                pass
            return False

        def _on_ctrl_i(event=None):
            if _kb_in_dialog_or_text():
                return
            try:
                self._set_loop_in()
            except Exception:
                pass
            return "break"
        def _on_ctrl_o(event=None):
            if _kb_in_dialog_or_text():
                return
            try:
                self._set_loop_out()
            except Exception:
                pass
            return "break"
        def _on_l(event=None):
            if _kb_in_dialog_or_text():
                return
            try:
                self._toggle_loop()
            except Exception:
                pass
            return "break"

        # Remap Loop In to Ctrl+I
        self.root.bind("<Control-i>", _on_ctrl_i)
        # Remap Loop Out to Ctrl+O so plain 'o' can add OSC markers
        self.root.bind("<Control-o>", _on_ctrl_o)
        self.root.bind("<l>", _on_l)
        # Bind Delete key to remove selected items (OSC/MIDI/session/frame)
        try:
            self.root.bind("<Delete>", self._on_delete_key)
        except Exception:
            pass
        # Space bar toggles play/pause
        def _toggle_play_pause(event=None):
            try:
                if self.is_playing:
                    self._pause()
                else:
                    self._play()
            except Exception:
                pass
        # Bind globally and prevent default widget Space handling
        def _on_space(event=None):
            try:
                w = self.root.focus_get()
                if w is not None:
                    # If focus is inside a dialog (toplevel != root), don't toggle playback
                    try:
                        if w.winfo_toplevel() is not self.root:
                            return  # allow default handling (e.g., enter space in Entry)
                    except Exception:
                        pass
                    # If typing in text-like widgets, allow space character
                    cls = str(getattr(w, 'winfo_class', lambda: '')())
                    if cls in ("Entry", "TEntry", "Text", "Spinbox", "TSpinbox", "Combobox", "TCombobox"):
                        return
            except Exception:
                pass
            _toggle_play_pause()
            return "break"
        self.root.bind_all("<space>", _on_space)
        # Disable Space activation on button classes globally
        try:
            self.root.bind_class("TButton", "<space>", lambda e: "break")
            self.root.bind_class("Button", "<space>", lambda e: "break")
        except Exception:
            pass

        # Ensure buttons are never tab-stops to avoid Space activating them
        try:
            for widget in self.root.winfo_children():
                for child in widget.winfo_children():
                    if isinstance(child, (tk.Button, ttk.Button)):
                        try:
                            child.configure(takefocus=0)
                        except Exception:
                            pass
        except Exception:
            pass
        
        view_menu = tk.Menu(menu_bar, tearoff=0)
        view_menu.add_command(label="Toggle DMX Monitor", command=self._toggle_monitor, accelerator="Ctrl+M")
        view_menu.add_command(label="DMX Channel Filter", command=self._open_dmx_filter)
        view_menu.add_separator()
        view_menu.add_command(label="Zoom In", command=lambda: self._zoom(10), accelerator="+")
        view_menu.add_command(label="Zoom Out", command=lambda: self._zoom(-10), accelerator="-")
        view_menu.add_command(label="Fit Timeline", command=self._zoom_fit)
        self.root.bind("<Control-m>", lambda e: self._toggle_monitor())

        # Help menu with Keyboard Shortcuts
        help_menu = tk.Menu(menu_bar, tearoff=0)
        help_menu.add_command(label="Keyboard Shortcuts", command=self._show_keyboard_shortcuts)
        help_menu.add_separator()
        def _open_verbose_log():
            try:
                path = _VERBOSE_FILE
                # Use platform-appropriate opener
                if sys.platform == "darwin":
                    import subprocess
                    subprocess.Popen(["open", path])
                elif os.name == "nt":
                    os.startfile(path)
                else:
                    import subprocess
                    subprocess.Popen(["xdg-open", path])
            except Exception as e:
                try:
                    debug_log(f"ERROR: Open verbose log failed: {e}")
                except Exception:
                    pass
                messagebox.showerror("Open Log Failed", str(e))
        help_menu.add_command(label="Open Verbose Log", command=_open_verbose_log)
        help_menu.add_command(label="About", command=self._show_about)

        # Arrange menu bar order: File, Edit, View, Playback, Record, Settings, Help
        try:
            # Re-attach menus in desired order
            menu_bar.delete(0, tk.END)
        except Exception:
            pass
        menu_bar.add_cascade(label="File", menu=file_menu)
        menu_bar.add_cascade(label="Edit", menu=edit_menu)
        menu_bar.add_cascade(label="View", menu=view_menu)
        menu_bar.add_cascade(label="Playback", menu=playback_menu)
        # Record as top-level after Playback
        menu_bar.add_cascade(label="Record", menu=record_menu)
        menu_bar.add_cascade(label="Settings", menu=settings_menu)
        menu_bar.add_cascade(label="Help", menu=help_menu)

        # Keyboard zoom shortcuts: '+' to zoom in, '-' to zoom out
        def _on_zoom_in(event=None):
            # Avoid triggering while typing in text-like widgets or dialogs
            if _kb_in_dialog_or_text():
                return
            try:
                self._zoom(10)
            except Exception:
                pass
            return "break"
        def _on_zoom_out(event=None):
            if _kb_in_dialog_or_text():
                return
            try:
                self._zoom(-10)
            except Exception:
                pass
            return "break"
        # Bind common keysyms including keypad variants; use bind_all so focus doesn't block
        try:
            # Plus can arrive as 'plus', 'Shift-=' on US keyboards, and keypad add
            self.root.bind_all("<KeyPress-plus>", _on_zoom_in)
            self.root.bind_all("<KeyPress-=>", _on_zoom_in)  # Shift+='+'
            self.root.bind_all("<KP_Add>", _on_zoom_in)
            # Minus and keypad subtract
            self.root.bind_all("<KeyPress-minus>", _on_zoom_out)
            self.root.bind_all("<KP_Subtract>", _on_zoom_out)
        except Exception:
            pass
        
        # Main container
        main_frame = ttk.Frame(self.root, style="White.TFrame")
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Header with logo and title
        header_frame = ttk.Frame(main_frame, style="White.TFrame")
        header_frame.pack(fill=tk.X, pady=(0, 6))
        # Load logo if available (prefer PIL for smoother scaling)
        self._header_logo_img = None
        try:
            logo_candidates = [
                os.path.join(os.path.dirname(__file__), "logo.png"),
                os.path.join(os.path.dirname(__file__), "assets", "logo.png"),
                os.path.join(os.path.dirname(os.path.dirname(__file__)), "logo.png"),
            ]
            for p in logo_candidates:
                if os.path.exists(p):
                    # Prefer PIL for high-quality resize preserving aspect ratio
                    try:
                        from PIL import Image, ImageTk
                        im = Image.open(p).convert("RGBA")
                        # Target max height 80px, width up to 300px (larger)
                        target_h, target_w = 80, 300
                        im.thumbnail((target_w, target_h), resample=Image.LANCZOS)
                        self._header_logo_img = ImageTk.PhotoImage(im)
                        break
                    except Exception:
                        # Fallback to Tk PhotoImage without rough subsampling if small enough
                        try:
                            img = tk.PhotoImage(file=p)
                            if img.height() > target_h or img.width() > target_w:
                                # As last resort, apply integer subsample to reduce size
                                h_factor = max(1, img.height() // target_h)
                                w_factor = max(1, img.width() // target_w)
                                factor = max(1, min(h_factor, w_factor))
                                img = img.subsample(factor)
                            self._header_logo_img = img
                            break
                        except Exception:
                            self._header_logo_img = None
        except Exception:
            self._header_logo_img = None
        # Logo in header removed per request; using space for status controls only
        # Remove the text next to the logo for a cleaner header
        # Spacer to push any right-side info
        ttk.Label(header_frame, text="").pack(side=tk.LEFT, expand=True)
        # Right-side compact panel for status controls
        right_panel = ttk.Frame(header_frame)
        right_panel.pack(side=tk.RIGHT)
        # (Temporary pane info button removed)

        # Transport toolbar (top)
        toolbar_frame = ttk.Frame(main_frame)
        toolbar_frame.pack(fill=tk.X, pady=(0, 2))
        
        ttk.Button(toolbar_frame, text="⏮ Rewind", command=self._rewind, takefocus=0).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar_frame, text="▶ Play", command=self._play, takefocus=0).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar_frame, text="⏸ Pause", command=self._pause, takefocus=0).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar_frame, text="⏹ Stop", command=self._stop, takefocus=0).pack(side=tk.LEFT, padx=2)
        # Record toggle button (single button: click to start/stop)
        def _toggle_recording():
            try:
                if not self.recording:
                    self._start_recording()
                    try:
                        self.record_btn.configure(text="● Recording", bg="#c62828", fg="white", activebackground="#b71c1c", activeforeground="white")
                    except Exception:
                        pass
                else:
                    self._stop_recording()
                    try:
                        self.record_btn.configure(text="● Record", bg="#424242", fg="white", activebackground="#2c2c2c", activeforeground="white")
                    except Exception:
                        pass
            except Exception:
                pass
        self.record_btn = tk.Button(toolbar_frame, text="● Record", command=_toggle_recording, takefocus=0,
                                    bg="#424242", fg="white", activebackground="#2c2c2c", activeforeground="white", width=12,
                                    relief=tk.RAISED, bd=2)
        self.record_btn.pack(side=tk.LEFT, padx=8)
        # Secondary control panel (below toolbar)
        control_frame = ttk.Frame(main_frame)
        control_frame.pack(fill=tk.X, pady=5)
        ttk.Separator(control_frame, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=8)
        # Logging toggle (moved to header right panel)
        def _toggle_verbose():
            try:
                self.verbose_logging = not self.verbose_logging
                self.settings["verbose_logging"] = self.verbose_logging
                set_verbose_logging(self.verbose_logging)
                self._save_settings()
                # Update button color/state
                try:
                    if self.verbose_logging:
                        self.verbose_btn.configure(bg="#c62828", fg="white", activebackground="#b71c1c", activeforeground="white")
                        try:
                            debug_log("Verbose logging enabled")
                        except Exception:
                            pass
                    else:
                        self.verbose_btn.configure(bg="#424242", fg="white", activebackground="#2c2c2c", activeforeground="white")
                        try:
                            debug_log("Verbose logging disabled")
                        except Exception:
                            pass
                except Exception:
                    pass
                self._show_status("Verbose logging ON" if self.verbose_logging else "Verbose logging OFF")
            except Exception:
                pass
        # Use tk.Button so we can color it (ttk doesn't support bg easily)
        init_bg = "#c62828" if getattr(self, "verbose_logging", False) else "#424242"
        init_abg = "#b71c1c" if getattr(self, "verbose_logging", False) else "#2c2c2c"
        self.verbose_btn = tk.Button(right_panel, text="Verbose Log", command=_toggle_verbose, takefocus=0,
                                     bg=init_bg, fg="white", activebackground=init_abg, activeforeground="white", width=12,
                                     relief=tk.RAISED, bd=2)
        self.verbose_btn.pack(side=tk.RIGHT, padx=6)

        self.capture_indicator = tk.Label(right_panel, text="CAPTURE OFF", bg="#2b2b2b", fg="lightgray",
                         width=12, relief=tk.SUNKEN, bd=1)
        self.capture_indicator.pack(side=tk.RIGHT, padx=6)
        # Enable session priority checkbox
        def _toggle_priority():
            try:
                self.session_priority_enabled = not self.session_priority_enabled
                try:
                    if hasattr(self, 'session_priority_var') and self.session_priority_var:
                        self.session_priority_var.set(self.session_priority_enabled)
                except Exception:
                    pass
                self._show_status("Session Priority ON" if self.session_priority_enabled else "Session Priority OFF")
            except Exception:
                pass
        self.session_priority_var = tk.BooleanVar(value=self.session_priority_enabled)
        ttk.Checkbutton(right_panel, text="Session Priority", command=_toggle_priority, variable=self.session_priority_var).pack(side=tk.RIGHT, padx=6)
        # Ignore-on-Capture status label
        self.ignore_status = ttk.Label(right_panel, text="Ignore: OFF", foreground="lightgray")
        self.ignore_status.pack(side=tk.RIGHT, padx=6)
        def _refresh_ignore_status():
            try:
                if getattr(self, "ignored_on_capture_enabled", False):
                    uni_count = len([u for u, chans in getattr(self, "ignored_on_capture", {}).items() if chans])
                    ch_count = sum(len(chans) for chans in getattr(self, "ignored_on_capture", {}).values())
                    self.ignore_status.config(text=f"Ignore: {uni_count}U/{ch_count}ch", foreground="orange")
                else:
                    self.ignore_status.config(text="Ignore: OFF", foreground="lightgray")
            except Exception:
                pass
        self._refresh_ignore_status = _refresh_ignore_status
        self._refresh_ignore_status()
        
        ttk.Label(control_frame, text="Zoom (+/-):").pack(side=tk.LEFT, padx=(6, 2))
        ttk.Button(control_frame, text="-", command=lambda: self._zoom(-10), width=3).pack(side=tk.LEFT)
        ttk.Button(control_frame, text="+", command=lambda: self._zoom(10), width=3).pack(side=tk.LEFT, padx=2)
        ttk.Button(control_frame, text="Fit Timeline", command=self._zoom_fit).pack(side=tk.LEFT, padx=4)
        
        # Move Universe, Speed, Target IP controls to Monitor area
        self.universe_var = tk.StringVar(value=str(self.selected_universe))
        self.speed_var = tk.StringVar(value="1.0")
        self.target_var = tk.StringVar(value="255.255.255.255")
        
        ttk.Label(control_frame, text="Song:").pack(side=tk.LEFT, padx=(20, 2))
        ttk.Button(control_frame, text="Open Audio", command=self._open_audio, takefocus=0).pack(side=tk.LEFT, padx=2)
        self.audio_label = ttk.Label(control_frame, text="None", foreground="cyan", width=30)
        self.audio_label.pack(side=tk.LEFT, padx=2)
        
        # Timeline and monitor split with resizable divider
        # Use only supported options for PanedWindow (no highlightthickness/bd)
        self.paned_window = tk.PanedWindow(main_frame, orient=tk.HORIZONTAL, sashwidth=8, bg="#ffffff")
        self.paned_window.pack(fill=tk.BOTH, expand=True)
        
        # Left: Timeline canvas
        self.timeline_frame = ttk.LabelFrame(self.paned_window, text="Timeline", height=400, style="White.TLabelframe")
        self.paned_window.add(self.timeline_frame, stretch="always")
        
        self.canvas = tk.Canvas(self.timeline_frame, bg="#000000", height=300, cursor="crosshair", highlightthickness=0, bd=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self.canvas.bind("<Button-1>", self._on_canvas_click)
        self.canvas.bind("<B1-Motion>", self._on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_canvas_release)
        self.canvas.bind("<Button-3>", self._on_canvas_right_click)  # Right-click for delete
        # Hint: show zoom shortcuts when hovering over timeline
        try:
            self.canvas.bind("<Enter>", lambda e: self._show_status("Tip: Ctrl+Mousewheel or +/- to zoom timeline", timeout=2.5))
        except Exception:
            pass
        # Ctrl+MouseWheel zoom in/out, centered around playhead
        try:
            def _on_ctrl_wheel(event):
                try:
                    if getattr(event, "delta", 0) > 0:
                        self._zoom(10)
                    else:
                        self._zoom(-10)
                except Exception:
                    pass
                return "break"
            # Windows/macOS wheel
            self.canvas.bind("<Control-MouseWheel>", _on_ctrl_wheel)
            # Linux/X11 wheel buttons
            self.canvas.bind("<Control-Button-4>", lambda e: (_on_ctrl_wheel(type("E", (), {"delta": 120})()), "break") )
            self.canvas.bind("<Control-Button-5>", lambda e: (_on_ctrl_wheel(type("E", (), {"delta": -120})()), "break") )
        except Exception:
            pass
        self.canvas.bind("<Double-Button-1>", self._on_canvas_double_click)  # Double-click to edit
        self.root.bind("<Delete>", self._on_delete_key)  # Delete selected frame/session
        
        timeline_info_frame = ttk.Frame(self.timeline_frame)
        timeline_info_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(timeline_info_frame, text="Duration:").pack(side=tk.LEFT)
        self.duration_label = ttk.Label(timeline_info_frame, text="0:00.000", foreground="cyan")
        self.duration_label.pack(side=tk.LEFT, padx=10)
        
        ttk.Label(timeline_info_frame, text="Playhead:").pack(side=tk.LEFT)
        self.playhead_label = ttk.Label(timeline_info_frame, text="0:00.000", foreground="lime")
        self.playhead_label.pack(side=tk.LEFT, padx=10)
        
        ttk.Label(timeline_info_frame, text="Events:").pack(side=tk.LEFT)
        self.events_label = ttk.Label(timeline_info_frame, text="0", foreground="yellow")
        self.events_label.pack(side=tk.LEFT, padx=10)
        
        self.loop_label = ttk.Label(timeline_info_frame, text="", foreground="lime")
        self.loop_label.pack(side=tk.LEFT, padx=10)
        
        # Right: DMX monitor (compact by default; resizable)
        self.monitor_frame = ttk.LabelFrame(self.paned_window, text="DMX Monitor (All 512 Channels)", width=360, style="White.TLabelframe")
        self.paned_window.add(self.monitor_frame, stretch="never")
        # If no saved sash settings, use the current pane location as the default
        try:
            if "monitor_sash_ratio" not in self.settings and "monitor_sash_left_px" not in self.settings:
                # Allow initial layout to settle, then capture current sash
                def _capture_initial_sash():
                    try:
                        total_w = self.paned_window.winfo_width()
                        left_w = self.timeline_frame.winfo_width()
                        if total_w and left_w:
                            ratio = max(0.2, min(0.95, left_w / total_w))
                            self.settings["monitor_sash_ratio"] = ratio
                            self.settings["monitor_sash_left_px"] = int(left_w)
                            self._save_settings()
                            if self.verbose_logging:
                                debug_log(f"SASH INIT DEFAULT: total_w={total_w} left_w={left_w} ratio={ratio:.3f}")
                    except Exception:
                        pass
                self.root.after(250, _capture_initial_sash)
        except Exception:
            pass
        # Restore saved sash ratio if present; else default to 70% timeline
        def _restore_sash(retry=0):
            try:
                total_w = self.paned_window.winfo_width()
                # Ensure panes exist and we have a usable width
                panes = getattr(self.paned_window, 'panes', lambda: [])()
                if total_w is None or total_w < 100 or not panes or len(panes) < 2:
                    if retry < 10:
                        self.root.after(200, lambda: _restore_sash(retry + 1))
                    return
                # Prefer persisted pixel width if present; fallback to ratio
                left_px = int(self.monitor_sash_left_px) if int(self.monitor_sash_left_px) > 0 else None
                ratio = float(self.monitor_sash_ratio)
                ratio = 0.7 if ratio <= 0 or ratio >= 1 else ratio
                left_w = left_px if left_px else int(total_w * ratio)
                # Clamp to sensible bounds to avoid hiding the timeline
                min_left = max(300, int(total_w * 0.2))
                max_left = max(min_left + 200, int(total_w * 0.95))
                left_w = max(min_left, min(left_w, max_left))
                if self.verbose_logging:
                    try:
                        debug_log(f"SASH RESTORE: total_w={total_w} ratio={ratio:.3f} left_w={left_w} panes={len(panes)} retry={retry}")
                    except Exception:
                        pass
                try:
                    self.paned_window.sash_place(0, left_w, 0)
                except Exception:
                    if retry < 10:
                        self.root.after(200, lambda: _restore_sash(retry + 1))
            except Exception:
                pass
        self.root.after(300, _restore_sash)
        # Also restore once more after initial layout settles
        self.root.after(1000, _restore_sash)
        # Enforce a locked sash position per user request
        try:
            self.monitor_sash_left_px = 1053
            def _enforce_locked_sash(event=None):
                try:
                    self.paned_window.sash_place(0, int(self.monitor_sash_left_px), 0)
                except Exception:
                    pass
            # Enforce after layout settles and on pane configure
            self.root.after(1200, _enforce_locked_sash)
            self.paned_window.bind("<Configure>", _enforce_locked_sash)
        except Exception:
            pass

        # Report pane dimensions after user adjusts the sash
        def _report_sash(event=None):
            try:
                total_w = self.paned_window.winfo_width()
                left_w = self.timeline_frame.winfo_width()
                right_w = self.monitor_frame.winfo_width()
                msg = (
                    f"Pane Sizes:\n"
                    f"Total Width: {total_w}\n"
                    f"Timeline (left): {left_w}\n"
                    f"DMX Monitor (right): {right_w}\n\n"
                    f"Sash Position (left width): {left_w}"
                )
                try:
                    messagebox.showinfo("Pane Dimensions", msg)
                except Exception:
                    debug_log(msg)
            except Exception as e:
                debug_log(f"SASH REPORT ERROR: {e}")
        # Hook into existing sash events to report dimensions after changes
        try:
            def _report_after_save(event=None):
                try:
                    self.root.after(10, _report_sash)
                except Exception:
                    pass
            self.paned_window.bind("<ButtonRelease-1>", _report_after_save)
            self.paned_window.bind("<B1-Motion>", _report_after_save)
            self.paned_window.bind("<Configure>", _report_after_save)
        except Exception:
            pass

        # Save sash ratio on user adjustment
        def _save_sash_ratio(event=None):
            try:
                # Compute ratio from actual pane widths to avoid coord quirks
                total_w = self.paned_window.winfo_width()
                left_w = self.timeline_frame.winfo_width()
                if total_w and left_w:
                    ratio = max(0.2, min(0.95, left_w / total_w))
                    self.settings["monitor_sash_ratio"] = ratio
                    self.settings["monitor_sash_left_px"] = int(left_w)
                    self._save_settings()
                    if self.verbose_logging:
                        try:
                            debug_log(f"SASH SAVE: total_w={total_w} left_w={left_w} ratio={ratio:.3f}")
                        except Exception:
                            pass
            except Exception:
                pass
        # Bind to sash movement (drag and release) and window resize
        self.paned_window.bind("<B1-Motion>", _save_sash_ratio)
        self.paned_window.bind("<ButtonRelease-1>", _save_sash_ratio)
        self.paned_window.bind("<Configure>", _save_sash_ratio)
        # Ensure save also occurs after app resize events at root level
        self.root.bind("<Configure>", _save_sash_ratio)
        # Persist window size and maximize state
        def _save_window_geometry(event=None):
            try:
                # If maximized, remember state; else capture size
                is_zoomed = False
                try:
                    is_zoomed = (self.root.state() == "zoomed")
                except Exception:
                    pass
                self.settings["window_maximized"] = bool(is_zoomed)
                if not is_zoomed:
                    w = self.root.winfo_width()
                    h = self.root.winfo_height()
                    if w and h:
                        self.settings["window_width"] = int(w)
                        self.settings["window_height"] = int(h)
                self._save_settings()
            except Exception:
                pass
        self.root.bind("<Configure>", _save_window_geometry)
        
        # Initialize DMX labels dictionary
        self.dmx_labels = {}
        
        # Create the monitor layout (will use filter if enabled)
        self._update_dmx_monitor_layout()
        
        # Bind frame resize events to rebuild monitor layout
        self.monitor_frame.bind("<Configure>", self._on_monitor_frame_resize)
        
        # Start DMX monitor update loop
        self._update_dmx_monitor_loop()
    
    def _edit_session_priorities(self):
        """Open dialog to edit per-session priorities."""
        dlg = tk.Toplevel(self.root)
        dlg.title("Edit Session Priorities")
        dlg.geometry("500x420")
        dlg.configure(bg="gray20")
        dlg.transient(self.root)
        dlg.grab_set()

        ttk.Label(dlg, text="1 is highest; smaller numbers override when enabled.", foreground="white", background="gray20").pack(pady=8)

        frame = ttk.Frame(dlg, padding=10)
        frame.pack(fill=tk.BOTH, expand=True)

        # Table headers
        hdr = ttk.Frame(frame)
        hdr.pack(fill=tk.X)
        ttk.Label(hdr, text="Session", width=12).pack(side=tk.LEFT)
        ttk.Label(hdr, text="Name", width=20).pack(side=tk.LEFT)
        ttk.Label(hdr, text="Priority", width=12).pack(side=tk.LEFT)

        # Scrollable list
        canvas = tk.Canvas(frame, bg="gray20", highlightthickness=0)
        scroll = ttk.Scrollbar(frame, orient="vertical", command=canvas.yview)
        inner = ttk.Frame(canvas)
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0,0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set, height=280)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)

        # Collect sessions
        sessions = sorted({e.get('session',1) for e in (self.timeline_data or [])})
        spin_vars = {}
        for s_id in sessions:
            row = ttk.Frame(inner)
            row.pack(fill=tk.X, pady=3)
            ttk.Label(row, text=f"{s_id}", width=12).pack(side=tk.LEFT)
            name = self.session_names.get(s_id, f"Session {s_id}")
            ttk.Label(row, text=name, width=20).pack(side=tk.LEFT)
            pr = int(self.session_priorities.get(s_id, s_id))
            var = tk.IntVar(value=pr)
            spin = ttk.Spinbox(row, from_=0, to=999, textvariable=var, width=6)
            spin.pack(side=tk.LEFT)
            spin_vars[s_id] = var

        # Buttons
        btns = ttk.Frame(dlg, padding=10)
        btns.pack(fill=tk.X)
        def save_priorities():
            try:
                for s_id, var in spin_vars.items():
                    self.session_priorities[s_id] = int(var.get())
                self._show_status("Session priorities saved")
                dlg.destroy()
            except Exception as e:
                messagebox.showerror("Error", str(e))
        ttk.Button(btns, text="Save", command=save_priorities).pack(side=tk.RIGHT, padx=6)
        ttk.Button(btns, text="Close", command=dlg.destroy).pack(side=tk.RIGHT)

    def _open_audio(self):
        """Load an audio file (WAV, MP3, FLAC, OGG, etc.)."""
        file_path = filedialog.askopenfilename(
            filetypes=[
                ("Audio files", "*.wav *.mp3 *.flac *.ogg *.m4a"),
                ("WAV files", "*.wav"),
                ("MP3 files", "*.mp3"),
                ("FLAC files", "*.flac"),
                ("OGG files", "*.ogg"),
                ("All files", "*.*")
            ]
        )
        if file_path:
            try:
                fname = os.path.basename(file_path)
                ext = os.path.splitext(fname)[1].lower()
                
                # Check if audio libraries available for non-WAV
                if ext != '.wav' and not self.has_audio:
                    messagebox.showerror("Error", f"Cannot load {ext} files.\n\nMissing libraries.\n\nInstall: pip install mutagen soundfile")
                    return
                
                # Load WAV with wave module for waveform data
                if ext == '.wav':
                    with wave.open(file_path, 'rb') as wf:
                        self.audio_duration = wf.getnframes() / wf.getframerate()
                        frames = wf.readframes(wf.getnframes())
                        self.audio_data = struct.unpack(f'<{len(frames)//2}h', frames)
                else:
                    # For MP3, FLAC, OGG - use mutagen for duration, soundfile for waveform
                    if self.has_audio:
                        try:
                            # Get duration from metadata
                            audio_info = mutagen.File(file_path)
                            if audio_info and hasattr(audio_info.info, 'length'):
                                self.audio_duration = audio_info.info.length
                            else:
                                self.audio_duration = 0.0
                            
                            # Try to load waveform data with soundfile
                            try:
                                data, samplerate = sf.read(file_path)
                                # Convert to mono if stereo
                                if len(data.shape) > 1:
                                    data = np.mean(data, axis=1)
                                # Convert to int16 range for consistency
                                self.audio_data = (data * 32767).astype(np.int16).tolist()
                            except:
                                # If soundfile can't decode, just use duration without waveform
                                self.audio_data = None
                        except Exception as e:
                            messagebox.showerror("Error", f"Failed to load {ext}: {e}")
                            return
                
                self.audio_file = file_path
                self.audio_label.config(text=fname, foreground="lime")
                
                # Reset playhead to beginning
                self.playhead_pos = 0.0
                
                # Zoom to fit the entire audio file in view
                self.waveform_cached = False
                self._zoom_fit()
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load audio: {e}")
    
    def _open_timeline(self):
        """Load a timeline file."""
        file_path = filedialog.askopenfilename(
            filetypes=[("Timeline files", "*.timeline *.gz *.mpk"), ("All files", "*.*")]
        )
        if file_path:
            try:
                try:
                    debug_log(f"FILE OPEN: {file_path}")
                except Exception:
                    pass
                from timeline.format import load_timeline
                self.timeline_data = load_timeline(file_path)
                # Normalize event fields to avoid type issues
                normalized = []
                for evt in self.timeline_data:
                    if not isinstance(evt, dict):
                        continue
                    t = evt.get("t", 0)
                    try:
                        t = float(t)
                    except Exception:
                        t = 0.0
                    universe = evt.get("universe", 0)
                    try:
                        universe = int(universe)
                    except Exception:
                        universe = 0
                    opcode = evt.get("opcode", 80)
                    try:
                        opcode = int(opcode)
                    except Exception:
                        opcode = 80
                    session = evt.get("session", 1)
                    try:
                        session = int(session)
                    except Exception:
                        session = 1
                    payload = evt.get("payload")
                    normalized.append({"t": t, "universe": universe, "opcode": opcode, "session": session, "payload": payload})
                self.timeline_data = normalized
                self.playhead_pos = 0.0
                # Initialize capture session counter based on existing sessions in file
                try:
                    existing_sessions = [e.get("session", 1) for e in self.timeline_data]
                    max_session = max(existing_sessions) if existing_sessions else 0
                    self.capture_session = int(max_session)
                    self.current_session_id = int(max_session)
                except Exception:
                    # Fallback: leave counters as-is
                    pass
                
                # Load associated audio file if it exists
                import json
                metadata_path = file_path + ".meta"
                if os.path.exists(metadata_path):
                    try:
                        with open(metadata_path, 'r') as f:
                            metadata = json.load(f)
                            audio_path = metadata.get("audio_file")
                            if audio_path and os.path.exists(audio_path):
                                # Programmatically load the audio file
                                self.audio_file = audio_path
                                fname = os.path.basename(audio_path)
                                
                                # Load audio data based on format
                                ext = os.path.splitext(fname)[1].lower()
                                if ext == '.wav':
                                    with wave.open(audio_path, 'rb') as wf:
                                        self.audio_duration = wf.getnframes() / wf.getframerate()
                                        frames = wf.readframes(wf.getnframes())
                                        self.audio_data = struct.unpack(f'<{len(frames)//2}h', frames)
                                else:
                                    # For other formats, use mutagen + soundfile
                                    try:
                                        import mutagen
                                        import soundfile as sf
                                        import numpy as np
                                        
                                        audio_info = mutagen.File(audio_path)
                                        if audio_info and hasattr(audio_info.info, 'length'):
                                            self.audio_duration = audio_info.info.length
                                        
                                        try:
                                            data, samplerate = sf.read(audio_path)
                                            if len(data.shape) > 1:
                                                data = np.mean(data, axis=1)
                                            self.audio_data = (data * 32767).astype(np.int16).tolist()
                                        except:
                                            self.audio_data = None
                                    except:
                                        pass
                                
                                self.audio_label.config(text=fname, foreground="lime")
                            
                            # Load session names, markers, loop state, and network prefs
                            self.session_names = metadata.get("session_names", {})
                            # Convert string keys back to integers for session_names
                            self.session_names = {int(k): v for k, v in self.session_names.items()}
                            self.markers = metadata.get("markers", [])
                            # Load MIDI markers and normalize types
                            raw_midi = metadata.get("midi_markers", [])
                            normalized_midi = []
                            for m in raw_midi:
                                if not isinstance(m, dict):
                                    continue
                                try:
                                    t = float(m.get("t", 0.0))
                                except Exception:
                                    t = 0.0
                                try:
                                    note = int(m.get("note", 0))
                                except Exception:
                                    note = 0
                                try:
                                    velocity = int(m.get("velocity", 0))
                                except Exception:
                                    velocity = 0
                                try:
                                    channel = int(m.get("channel", 1))
                                except Exception:
                                    channel = 1
                                try:
                                    duration = float(m.get("duration", 0.0))
                                except Exception:
                                    duration = 0.0
                                label = m.get("label", "")
                                normalized_midi.append({
                                    "t": t,
                                    "note": note,
                                    "velocity": velocity,
                                    "channel": channel,
                                    "duration": duration,
                                    "label": label
                                })
                            self.midi_markers = normalized_midi
                            # Load OSC markers and normalize types
                            raw_osc = metadata.get("osc_markers", [])
                            normalized_osc = []
                            for m in raw_osc:
                                if not isinstance(m, dict):
                                    continue
                                try:
                                    t = float(m.get("t", 0.0))
                                except Exception:
                                    t = 0.0
                                name = str(m.get("name", "OSC"))
                                ip = str(m.get("ip", "127.0.0.1"))
                                try:
                                    port = int(m.get("port", 8000))
                                except Exception:
                                    port = 8000
                                address = str(m.get("address", "/"))
                                args = m.get("args", [])
                                if not isinstance(args, list):
                                    args = [str(args)]
                                normalized_osc.append({
                                    "t": t,
                                    "name": name,
                                    "ip": ip,
                                    "port": port,
                                    "address": address,
                                    "args": args
                                })
                            self.osc_markers = normalized_osc
                            # Load recent OSC IPs list
                            try:
                                ips = metadata.get("recent_osc_ips", [])
                                if isinstance(ips, list):
                                    self.recent_osc_ips = [str(ip) for ip in ips if isinstance(ip, (str, int, float))]
                            except Exception:
                                pass
                            self.loop_enabled = metadata.get("loop_enabled", False)
                            self.loop_start = metadata.get("loop_start", 0.0)
                            self.loop_end = metadata.get("loop_end", 0.0)
                            # Load OSC network interface preference
                            try:
                                self.osc_network_interface = metadata.get("osc_network_interface", self.settings.get("osc_network_interface", "0.0.0.0"))
                            except Exception:
                                self.osc_network_interface = self.settings.get("osc_network_interface", "0.0.0.0")
                            # Load session priority settings (optional)
                            try:
                                pr_enabled = metadata.get("session_priority_enabled", False)
                                pr_map = metadata.get("session_priorities", {})
                                # Convert keys back to int if saved as strings
                                if isinstance(pr_map, dict):
                                    pr_map = {int(k): int(v) for k, v in pr_map.items() if str(k).isdigit()}
                                self.session_priority_enabled = bool(pr_enabled)
                                self.session_priorities = pr_map if isinstance(pr_map, dict) else {}
                                try:
                                    debug_log(f"META LOAD: session_priority_enabled={self.session_priority_enabled} sessions={len(self.session_priorities)}")
                                except Exception:
                                    pass
                                # Reflect in UI checkbox if available
                                try:
                                    if hasattr(self, 'session_priority_var') and self.session_priority_var:
                                        self.session_priority_var.set(self.session_priority_enabled)
                                except Exception:
                                    pass
                            except Exception:
                                pass
                    except:
                        pass
                
                self.waveform_cached = False
                try:
                    self._update_canvas_view()
                except Exception:
                    # Silently ignore canvas update errors on load - data is already loaded
                    pass
                # Zoom to fit the loaded timeline (events, markers, MIDI)
                try:
                    self._zoom_fit()
                except Exception:
                    pass
            except Exception as e:
                try:
                    debug_log(f"ERROR: File open failed for {file_path}: {e}")
                except Exception:
                    pass
                # Only show error if timeline data failed to load
                if not self.timeline_data:
                    messagebox.showerror("Error", f"Failed to load timeline: {e}")
    
    def _save_timeline(self):
        """Save timeline (all captures) with audio file reference."""
        # Use full timeline_data if available, otherwise fall back to recorded_events
        data_to_save = self.timeline_data if self.timeline_data else self.recorded_events
        # Allow saving when there are MIDI markers or markers even if no DMX events
        if not data_to_save and not self.midi_markers and not self.markers:
            messagebox.showwarning("Warning", "No events or markers to save")
            return
        
        file_path = filedialog.asksaveasfilename(
            defaultextension=".timeline",
            filetypes=[("Timeline JSON", "*.timeline"), ("Compressed", "*.timeline.gz")]
        )
        if file_path:
            try:
                try:
                    debug_log(f"FILE SAVE: {file_path}")
                except Exception:
                    pass
                from timeline.format import save_timeline
                import json
                
                # Save timeline (DMX events may be empty if only markers/MIDI are present)
                save_timeline(data_to_save or [], file_path)
                
                # Save metadata with audio file path, session names, markers, and loop
                metadata = {
                    "audio_file": self.audio_file if self.audio_file else None,
                    "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
                    "events_count": len(data_to_save),
                    "session_names": self.session_names,
                    "markers": self.markers,
                    "midi_markers": self.midi_markers,
                    "osc_markers": self.osc_markers,
                    # Persist list of recent OSC target IPs for dropdowns
                    "recent_osc_ips": getattr(self, "recent_osc_ips", []),
                    "loop_enabled": self.loop_enabled,
                    "loop_start": self.loop_start,
                    "loop_end": self.loop_end,
                    # Persist session priority configuration (optional)
                    "session_priority_enabled": getattr(self, "session_priority_enabled", False),
                    # Ensure JSON-serializable keys (convert to strings)
                    "session_priorities": {str(k): int(v) for k, v in getattr(self, "session_priorities", {}).items()},
                    # Persist OSC network interface selection
                    "osc_network_interface": getattr(self, "osc_network_interface", self.settings.get("osc_network_interface", "0.0.0.0"))
                }
                
                metadata_path = file_path + ".meta"
                with open(metadata_path, 'w') as f:
                    json.dump(metadata, f, indent=2)
                try:
                    debug_log(f"META SAVE: session_priority_enabled={metadata.get('session_priority_enabled', False)} sessions={len(metadata.get('session_priorities', {}))}")
                except Exception:
                    pass
                
                messagebox.showinfo("Success", f"Timeline and audio reference saved to {file_path}")
            except Exception as e:
                try:
                    debug_log(f"ERROR: File save failed for {file_path}: {e}")
                except Exception:
                    pass
                messagebox.showerror("Error", f"Failed to save timeline: {e}")
    
    def _start_recording(self):
        """Start recording Art-Net packets."""
        if self.recording:
            return
        
        if not self.audio_file:
            return

        # Start a new capture session and keep prior captures on the timeline
        self.capture_session += 1
        self.current_session_id = self.capture_session
        # Default priority: newest session highest unless edited
        try:
            self.session_priorities[self.current_session_id] = self.current_session_id
        except Exception:
            pass
        self.recording = True
        self.recorded_events = []
        
        # Preserve current playhead position if already playing, otherwise start from beginning
        recording_start_offset = self.playhead_pos if self.is_playing else 0.0
        if not self.is_playing:
            self.playhead_pos = 0.0
            # Start audio playback from beginning
            self._play_audio()
        # If already playing, don't restart audio
        
        # Start playhead animation for visual feedback
        was_already_playing = self.is_playing
        self.is_playing = True
        
        # Update capture indicator
        self._set_record_indicator(True)
        def recording_playhead_thread():
            start_time = time.perf_counter()
            last_update = 0
            while self.recording and self.is_playing:
                self.playhead_pos = recording_start_offset + (time.perf_counter() - start_time)
                
                # Update UI only every 100ms to prevent freezing
                if self.playhead_pos - last_update >= 0.1:
                    self.root.after(0, self._update_canvas_view)
                    last_update = self.playhead_pos
                
                time.sleep(0.05)
                
                # Stop when audio ends
                if self.playhead_pos >= self.audio_duration:
                    self.recording = False
                    self.is_playing = False
                    def _finalize_auto_stop():
                        try:
                            self._set_record_indicator(False)
                            # Reset Record toggle button visual state
                            try:
                                if hasattr(self, "record_btn") and self.record_btn:
                                    self.record_btn.configure(text="● Record", bg="#424242", fg="white", activebackground="#2c2c2c", activeforeground="white")
                            except Exception:
                                pass
                            # Append recorded events to timeline when auto-stopping at end of audio
                            if not self.timeline_data:
                                self.timeline_data = []
                            if getattr(self, 'recorded_events', None):
                                self.timeline_data.extend(self.recorded_events)
                            # Refresh view
                            self._update_canvas_view()
                        except Exception:
                            pass
                    self.root.after(0, _finalize_auto_stop)
                    break
        
        threading.Thread(target=recording_playhead_thread, daemon=True).start()
    
    def _stop_recording(self):
        """Stop recording."""
        if not self.recording:
            messagebox.showwarning("Warning", "Not recording")
            return
        
        self.recording = False
        self.is_playing = False
        self._stop_audio()
        # Update Record toggle button UI state
        try:
            if hasattr(self, "record_btn") and self.record_btn:
                self.record_btn.configure(text="● Record", bg="#424242", fg="white", activebackground="#2c2c2c", activeforeground="white")
        except Exception:
            pass
        
        # Transfer recorded events to timeline for visualization (append session)
        if not self.timeline_data:
            self.timeline_data = []
        self.timeline_data.extend(self.recorded_events)
        self._update_canvas_view()
        
        # Update capture indicator
        self._set_record_indicator(False)
        
        messagebox.showinfo("Stopped", f"Recorded {len(self.recorded_events)} events")
    
    def _rewind(self):
        """Rewind playhead to the beginning."""
        self._stop()  # Stop playback if playing
        self.playhead_pos = 0.0
        self.waveform_cached = False
        self._update_canvas_view()
    
    def _play(self):
        """Start playback."""
        if not self.timeline_data and not self.audio_file and not self.midi_markers:
            messagebox.showwarning("Warning", "Load a timeline/audio file or add MIDI markers first")
            return
        
        if self.is_playing:
            return
        
        # Stop any existing audio first to ensure clean start from new position
        self._stop_audio()
        
        self.is_playing = True
        self.waveform_cached = True  # Enable fast update mode
        speed = float(self.speed_var.get())
        target = self.target_var.get()
        
        try:
            debug_log(f"PLAY START: t={self.playhead_pos:.3f}, speed={speed}, target={target}, events={len(self.timeline_data) if self.timeline_data else 0}, midi={len(self.midi_markers)}, osc={len(self.osc_markers) if hasattr(self,'osc_markers') else 0}, audio={'yes' if self.audio_file else 'no'}")
        except Exception:
            pass

        def playback_thread():
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
                # Bind to selected interface to control egress
                try:
                    if self.network_interface:
                        sock.bind((self.network_interface, 0))
                except Exception:
                    pass
                
                # Start audio from current playhead position
                if self.audio_file:
                    self._play_audio()
                
                start_time = time.perf_counter()
                playback_start = self.playhead_pos
                
                # Calculate max duration from audio, timeline data, or MIDI markers
                if self.audio_file:
                    max_duration = self.audio_duration
                elif self.timeline_data:
                    max_duration = max([e.get('t', 0) for e in self.timeline_data], default=0)
                elif self.midi_markers:
                    max_duration = max([m['t'] + m.get('duration', 0.1) for m in self.midi_markers], default=10.0)
                else:
                    max_duration = 10.0  # Default 10 seconds for empty timeline
                
                # Prepare events and priority map
                sorted_events = sorted(self.timeline_data, key=lambda e: e.get('t', 0)) if self.timeline_data else []
                # Change-only overlay state (per playback run)
                last_frame_by_session = {}
                last_sent_by_universe = {}
                allowed_sessions_by_universe = None
                if getattr(self, 'session_priority_enabled', False) and sorted_events:
                    # Compute the single winning session per universe for the whole playback window
                    winners = {}
                    for e in sorted_events:
                        u = e.get('universe', 0)
                        s_id = e.get('session', 1)
                        pr = int(self.session_priorities.get(s_id, 9999))
                        prev = winners.get(u)
                        if not prev or pr < prev[0]:
                            winners[u] = (pr, s_id)
                    allowed_sessions_by_universe = {u: s_id for u, (pr, s_id) in winners.items()}
                    try:
                        if self.verbose_logging:
                            debug_log(f"PRIORITY MAP: {allowed_sessions_by_universe}")
                    except Exception:
                        pass
                event_index = 0
                
                # Skip to events near the starting playhead position
                while event_index < len(sorted_events) and sorted_events[event_index].get('t', 0) < playback_start - 0.1:
                    event_index += 1
                
                # Playhead animation loop
                last_sent_time = playback_start - 1.0  # Track last sent time to avoid duplicates
                
                # Sort MIDI markers by time for efficient playback
                sorted_midi = sorted(self.midi_markers, key=lambda m: m['t']) if self.midi_markers else []
                debug_log(f"DEBUG: Prepared {len(sorted_midi)} MIDI markers for playback")
                midi_index = 0
                
                # Skip to MIDI markers near the starting playhead position
                while midi_index < len(sorted_midi) and sorted_midi[midi_index]['t'] < playback_start - 0.1:
                    midi_index += 1
                # Sort OSC markers by time
                sorted_osc = sorted(self.osc_markers, key=lambda m: m['t']) if self.osc_markers else []
                osc_index = 0
                while osc_index < len(sorted_osc) and sorted_osc[osc_index]['t'] < playback_start - 0.1:
                    osc_index += 1
                
                while self.is_playing:
                    elapsed = (time.perf_counter() - start_time) * speed
                    self.playhead_pos = playback_start + elapsed
                    
                    # Handle loop region
                    if self.loop_enabled and self.loop_end > self.loop_start:
                        if self.playhead_pos >= self.loop_end:
                            # Loop back to start
                            self.playhead_pos = self.loop_start
                            playback_start = self.loop_start
                            start_time = time.perf_counter()
                            
                            # Reset event index to loop start
                            event_index = 0
                            while event_index < len(sorted_events) and sorted_events[event_index].get('t', 0) < self.loop_start - 0.1:
                                event_index += 1
                            last_sent_time = self.loop_start - 1.0
                            
                            # Reset MIDI marker index to loop start
                            midi_index = 0
                            while midi_index < len(sorted_midi) and sorted_midi[midi_index]['t'] < self.loop_start - 0.1:
                                midi_index += 1
                            self.last_sent_midi = {}
                            
                            # Restart audio at loop start so sound loops with playhead
                            if self.audio_file:
                                try:
                                    self._stop_audio()
                                except Exception:
                                    pass
                                try:
                                    # _play_audio starts from current self.playhead_pos
                                    self._play_audio()
                                except Exception:
                                    pass
                    
                    # Update canvas
                    self.root.after(0, self._update_canvas_view)
                    
                    # Stop when audio ends (unless looping)
                    if not self.loop_enabled and self.playhead_pos >= max_duration:
                        break
                    
                    # Send DMX events for current time window (from last position to now)
                    if sorted_events:
                        # Collect events due in this tick
                        due_events = []
                        while event_index < len(sorted_events):
                            evt = sorted_events[event_index]
                            evt_time = evt.get('t', 0)
                            # Only include events up to the current playhead
                            if evt_time > self.playhead_pos:
                                break
                            if evt_time > last_sent_time:
                                due_events.append(evt)
                            event_index += 1

                        if due_events:
                            if getattr(self, 'session_priority_enabled', False):
                                # Change-only overlay: build a single merged frame per universe
                                # Collect latest packet per session per universe for this tick (support sparse events)
                                universe_session_packets = {}
                                for evt in due_events:
                                    u = int(evt.get('universe', 0))
                                    s_id = int(evt.get('session', 1))
                                    # Skip packets from non-winning sessions for that universe
                                    if allowed_sessions_by_universe and allowed_sessions_by_universe.get(u) != s_id:
                                        continue
                                    # Build DMX data, supporting sparse 'changes'
                                    changes = evt.get('changes') if evt.get('sparse') else None
                                    header = None
                                    dmx = bytearray(512)
                                    if changes:
                                        for ch, val in changes.items():
                                            if 0 <= int(ch) < 512:
                                                dmx[int(ch)] = int(val)
                                    else:
                                        payload_b64 = evt.get("payload", "")
                                        try:
                                            payload = base64.b64decode(payload_b64) if payload_b64 else b""
                                        except Exception:
                                            payload = b""
                                        header = payload[:18] if len(payload) >= 18 else None
                                        body = payload[18:18+512] if len(payload) > 18 else b""
                                        dmx = bytearray(body)
                                        if len(dmx) < 512:
                                            dmx.extend(b"\x00" * (512 - len(dmx)))
                                    universe_session_packets.setdefault(u, {})[s_id] = (header, dmx)

                                # Overlay only changed channels from higher-priority sessions
                                for u, session_map in universe_session_packets.items():
                                    # Sort sessions by priority ascending (1 highest)
                                    order = sorted(session_map.keys(), key=lambda sid: int(self.session_priorities.get(sid, 9999)))
                                    merged = bytearray(512)
                                    header = None
                                    # Base from lowest priority if exists, else zeros
                                    if order:
                                        base_sid = order[0]
                                        header, base_dmx = session_map[base_sid]
                                        merged[:] = base_dmx
                                        last_frame_by_session.setdefault(base_sid, {})
                                        last_frame_by_session[base_sid].setdefault(u, bytearray(512))
                                        last_frame_by_session[base_sid][u][:] = base_dmx
                                    # Overlay only if changed vs that session's last frame
                                    for sid in order[1:]:
                                        hdr, dmx = session_map[sid]
                                        if header is None:
                                            header = hdr
                                        last_frame_by_session.setdefault(sid, {})
                                        last_frame_by_session[sid].setdefault(u, bytearray(512))
                                        last = last_frame_by_session[sid][u]
                                        for ch in range(512):
                                            val = dmx[ch]
                                            if val != last[ch]:
                                                merged[ch] = val
                                        # Update last frame snapshot for change detection
                                        last_frame_by_session[sid][u][:] = dmx
                                    # Track last sent for universe
                                    last_sent_by_universe[u] = bytearray(merged)
                                    # Build packet and send
                                    pkt_header = header if header else b"Art-Net\x00\x00\x50\x00\x00\x00\x00\x00\x00\x00\x00"[:18]
                                    payload_data = pkt_header + bytes(merged)
                                    try:
                                        sock.sendto(payload_data, (target, 6454))
                                    except Exception:
                                        pass
                            else:
                                # No priority: send all due events in order (support sparse overlay)
                                to_send = sorted(due_events, key=lambda e: e.get('t', 0))

                            if not getattr(self, 'session_priority_enabled', False):
                                for evt in to_send:
                                    u = int(evt.get('universe', 0))
                                    if evt.get('sparse') and evt.get('changes'):
                                        # Overlay changes only
                                        base = last_sent_by_universe.get(u, bytearray(512))
                                        merged = bytearray(base)
                                        for ch, val in evt['changes'].items():
                                            ch_i = int(ch)
                                            if 0 <= ch_i < 512:
                                                merged[ch_i] = int(val)
                                        last_sent_by_universe[u] = bytearray(merged)
                                        header = b"Art-Net\x00\x00\x50\x00\x00\x00\x00\x00\x00\x00\x00"[:18]
                                        out = header + bytes(merged)
                                        try:
                                            sock.sendto(out, (target, 6454))
                                        except Exception:
                                            pass
                                    else:
                                        try:
                                            payload = base64.b64decode(evt.get("payload", "")) if evt.get("payload") else b""
                                        except Exception:
                                            payload = b""
                                        if payload:
                                            try:
                                                sock.sendto(payload, (target, 6454))
                                            except Exception:
                                                pass

                            last_sent_time = self.playhead_pos
                    
                    # Send MIDI markers for current time window
                    if sorted_midi:
                        while midi_index < len(sorted_midi):
                            midi_marker = sorted_midi[midi_index]
                            midi_time = midi_marker['t']
                            
                            # If MIDI marker is beyond current playhead, wait for next frame
                            if midi_time > self.playhead_pos + 0.05:
                                break
                            
                            # Send MIDI note if we haven't sent this one yet
                            marker_id = id(midi_marker)
                            if marker_id not in self.last_sent_midi or self.last_sent_midi[marker_id] < midi_time:
                                try:
                                    debug_log(f"DEBUG: Triggering MIDI at t={self.playhead_pos:.3f} for marker t={midi_time:.3f}")
                                    note = midi_marker.get('note', 60)
                                    velocity = midi_marker.get('velocity', 100)
                                    channel = midi_marker.get('channel', 1)
                                    duration = midi_marker.get('duration', 0.1)
                                    debug_log(f"DEBUG: MIDI params note={note} velocity={velocity} channel={channel} duration={duration} port={self.midi_output_port}")
                                    self._send_midi_note(note, velocity, channel, duration)
                                    self.last_sent_midi[marker_id] = midi_time
                                except Exception as e:
                                    print(f"MIDI playback error: {e}")
                            
                            midi_index += 1

                    # Send OSC markers for current time window
                    if sorted_osc:
                        while osc_index < len(sorted_osc):
                            osc_marker = sorted_osc[osc_index]
                            osc_time = osc_marker.get('t', 0.0)
                            if osc_time > self.playhead_pos + 0.05:
                                break
                            marker_id = id(osc_marker)
                            if marker_id not in self.last_sent_osc or self.last_sent_osc[marker_id] < osc_time:
                                try:
                                    ip = str(osc_marker.get('ip', '127.0.0.1'))
                                    port = int(osc_marker.get('port', 8000))
                                    address = str(osc_marker.get('address', '/'))
                                    args = osc_marker.get('args', [])
                                    self._send_osc(ip, port, address, args)
                                    self.last_sent_osc[marker_id] = osc_time
                                except Exception as e:
                                    debug_log(f"OSC playback error: {e}")
                            osc_index += 1
                    
                    time.sleep(0.016)  # ~60fps
                
                sock.close()
            except Exception as e:
                try:
                    debug_log(f"ERROR: Playback exception: {e}")
                except Exception:
                    pass
                messagebox.showerror("Playback Error", str(e))
            finally:
                self.is_playing = False
                self.waveform_cached = False
                self._stop_audio()
                self.last_sent_osc = {}
                try:
                    debug_log(f"PLAY END: t={self.playhead_pos:.3f}")
                except Exception:
                    pass
        
        threading.Thread(target=playback_thread, daemon=True).start()
    
    def _play_audio(self):
        """Play audio file using best available method."""
        if not self.audio_file:
            return
        
        try:
            # Use sounddevice for playback
            import soundfile as sf
            import sounddevice as sd
            data, samplerate = sf.read(self.audio_file)
            # Start from current playhead position
            start_sample = int(self.playhead_pos * samplerate)
            if start_sample < len(data):
                sd.play(data[start_sample:], samplerate, device=self.audio_device)
            return
        except Exception:
            pass

    def _begin_timecode_edit(self, event=None):
        """Replace the timecode label with an entry for inline editing."""
        try:
            # Prevent multiple editors
            if hasattr(self, "_timecode_entry") and self._timecode_entry:
                return
            # Create entry with current time text
            cur_text = self._format_time(self.playhead_pos)
            entry = tk.Entry(self.monitor_timecode_container if hasattr(self, "monitor_timecode_container") else self.monitor_frame,
                              bg="#ffffff", fg="#000000", font=("Segoe UI", 18, "bold"), justify="center")
            entry.insert(0, cur_text)
            # Place entry where the label is
            try:
                # Temporarily hide the label
                self.monitor_timecode_label.forget()
            except Exception:
                pass
            # Use pack for stable placement, avoid place() drift issues
            entry.pack(fill="x")
            self._timecode_entry = entry

            def _cancel(e=None):
                try:
                    # Restore label
                    if hasattr(self, "_timecode_entry") and self._timecode_entry:
                        try:
                            self._timecode_entry.place_forget()
                        except Exception:
                            pass
                        self._timecode_entry.destroy()
                        self._timecode_entry = None
                    self.monitor_timecode_label.pack(fill="x")
                except Exception:
                    pass

            def _apply(e=None):
                try:
                    val = entry.get().strip()
                    # Accept formats like HH:MM:SS.mmm or seconds (float)
                    new_pos = None
                    try:
                        # Try seconds float
                        new_pos = float(val)
                    except Exception:
                        # Try HH:MM:SS[.mmm]
                        parts = val.split(":")
                        if 1 <= len(parts) <= 3:
                            parts = [p.strip() for p in parts]
                            while len(parts) < 3:
                                parts.insert(0, "0")
                            h, m, s = parts
                            try:
                                h = int(h)
                                m = int(m)
                                s = float(s)
                                new_pos = max(0.0, h*3600 + m*60 + s)
                            except Exception:
                                pass
                    if new_pos is None:
                        # Invalid input: keep current and just cancel
                        _cancel()
                        return
                    # Update playhead safely
                    self.playhead_pos = float(new_pos)
                    # Refresh visuals on main thread
                    try:
                        self.root.after(0, self._update_canvas_view)
                    except Exception:
                        pass
                    # Restore label with new text
                    try:
                        self.monitor_timecode_label.config(text=self._format_time(self.playhead_pos))
                    except Exception:
                        pass
                    _cancel()
                except Exception:
                    _cancel()

            # Keep entry aligned on parent resize
            # Remove reposition handler; pack keeps it stable

            # Bind Enter to apply, Escape to cancel, focus the entry
            try:
                entry.bind("<Return>", _apply)
                entry.bind("<Escape>", _cancel)
                entry.focus_set()
                entry.selection_range(0, tk.END)
            except Exception:
                pass
        except Exception:
            pass
        
        try:
            # Fallback to winsound for WAV files
            if self.audio_file.lower().endswith('.wav'):
                import winsound
                winsound.PlaySound(self.audio_file, winsound.SND_FILENAME | winsound.SND_ASYNC)
                return
        except Exception:
            pass
    
    def _stop_audio(self):
        """Stop audio playback."""
        try:
            import sounddevice as sd
            sd.stop()
        except:
            pass
        
        try:
            import winsound
            winsound.PlaySound(None, winsound.SND_PURGE)
        except:
            pass
    
    def _pause(self):
        """Pause playback."""
        self.is_playing = False
        self._stop_audio()
        try:
            debug_log(f"PLAY PAUSE: t={self.playhead_pos:.3f}")
        except Exception:
            pass
    
    def _stop(self):
        """Stop playback/recording and reset."""
        self.is_playing = False
        # Stop recording using standard flow to append events and update UI
        if self.recording:
            try:
                self._stop_recording()
            except Exception:
                # Fallback: ensure flag off
                self.recording = False
        self._stop_audio()
        try:
            debug_log(f"PLAY STOP: t={self.playhead_pos:.3f}")
        except Exception:
            pass
        self.playhead_pos = 0.0
        self.last_sent_midi = {}  # Reset MIDI tracking
        self._update_canvas_view()
    
    def _zoom(self, delta):
        """Adjust zoom level centered on playhead position."""
        canvas_width = self.canvas.winfo_width()
        
        # Calculate playhead position in canvas before zoom
        playhead_x_before = self.playhead_pos * self.zoom_level
        
        # Calculate current scroll position
        scroll_pos = self.canvas.xview()[0]
        visible_start_time = scroll_pos * (self.canvas.winfo_reqwidth() / self.zoom_level if self.zoom_level > 0 else 0)
        
        # Update zoom level
        old_zoom = self.zoom_level
        self.zoom_level = max(10, self.zoom_level + delta)
        
        # Force canvas redraw
        self.waveform_cached = False
        self._update_canvas_view()
        
        # Calculate new playhead position in canvas after zoom
        playhead_x_after = self.playhead_pos * self.zoom_level
        
        # Adjust scroll to keep playhead centered in view
        max_time = max(
            self.audio_duration if self.audio_data else 0,
            max((evt.get("t", 0) for evt in self.timeline_data), default=0) if self.timeline_data else 0
        )
        total_width = int(max_time * self.zoom_level) + 100 if max_time > 0 else canvas_width
        
        if total_width > canvas_width:
            # Center view on playhead
            target_x = playhead_x_after - canvas_width / 2
            target_scroll = max(0, min(1.0, target_x / (total_width - canvas_width)))
            self.canvas.xview_moveto(target_scroll)

    def _show_keyboard_shortcuts(self):
        """Show a popup window listing all keyboard shortcuts."""
        try:
            top = tk.Toplevel(self.root)
            top.title("Keyboard Shortcuts")
            top.transient(self.root)
            top.grab_set()
            try:
                top.resizable(False, False)
            except Exception:
                pass
            container = ttk.Frame(top, padding=12)
            container.pack(fill=tk.BOTH, expand=True)

            ttk.Label(container, text="Keyboard Shortcuts", font=("Segoe UI", 12, "bold")).pack(anchor="w", pady=(0,8))

            shortcuts = [
                ("Play/Pause", "Space"),
                ("Undo", "Ctrl+Z"),
                ("Redo", "Ctrl+Y"),
                ("Toggle DMX Monitor", "Ctrl+M"),
                ("Loop In", "Ctrl+I"),
                ("Loop Out", "Ctrl+O"),
                ("Toggle Loop", "L"),
                ("Add MIDI Marker", "M"),
                ("Add OSC Marker", "o"),
                ("Delete Selected", "Delete"),
                ("Zoom In", "+ / Keypad +"),
                ("Zoom Out", "- / Keypad -"),
                ("Edit Timecode", "Double-click timecode; Enter/Escape to apply/cancel"),
            ]

            grid = ttk.Frame(container)
            grid.pack(fill=tk.BOTH, expand=True)
            for r, (name, accel) in enumerate(shortcuts):
                ttk.Label(grid, text=name, width=28, anchor="w").grid(row=r, column=0, sticky="w", padx=(0,12), pady=2)
                ttk.Label(grid, text=accel, foreground="#444444").grid(row=r, column=1, sticky="w", pady=2)

            btns = ttk.Frame(container)
            btns.pack(fill=tk.X, pady=(12,0))
            ttk.Button(btns, text="Close", command=top.destroy).pack(side=tk.RIGHT)
        except Exception:
            # Fallback to messagebox if layout fails
            try:
                import tkinter.messagebox as mb
                mb.showinfo("Keyboard Shortcuts", "Space: Play/Pause\nCtrl+Z: Undo\nCtrl+Y: Redo\nCtrl+M: Toggle DMX Monitor\nCtrl+I: Loop In\nCtrl+O: Loop Out\nL: Toggle Loop\nM: Add MIDI Marker\no: Add OSC Marker\nDelete: Delete Selected\n+: Zoom In\n-: Zoom Out\nDouble-click timecode: Edit\nEnter/Escape: Apply/Cancel")
            except Exception:
                pass

    def _show_about(self):
        """Show About dialog with build time/date and environment info."""
        try:
            import datetime
            import json
            # Determine build info strategy:
            # 1) If build_info.json exists alongside the script, prefer it
            # 2) Else use file modification time of this module as build time
            build_time_str = None
            build_source = "File modification time"
            try:
                here = os.path.dirname(__file__)
                bi_path = os.path.join(here, "build_info.json")
                if os.path.exists(bi_path):
                    with open(bi_path, "r", encoding="utf-8") as f:
                        info = json.load(f)
                    ts = info.get("build_time")
                    if ts is not None:
                        try:
                            # Accept ISO string (UTC 'Z' suffix supported) or epoch seconds
                            if isinstance(ts, (int, float)):
                                dt = datetime.datetime.fromtimestamp(ts)
                            else:
                                s = str(ts)
                                # Handle 'Z' by converting to +00:00 for fromisoformat
                                if s.endswith('Z'):
                                    s = s[:-1] + '+00:00'
                                dt = datetime.datetime.fromisoformat(s)
                            # Convert to local timezone for display
                            try:
                                dt_local = dt.astimezone()
                            except Exception:
                                dt_local = dt
                            build_time_str = dt_local.strftime("%Y-%m-%d %H:%M:%S")
                            build_source = "build_info.json"
                        except Exception:
                            build_time_str = str(ts)
                            build_source = "build_info.json"
                    else:
                        build_source = "build_info.json (missing build_time)"
            except Exception:
                pass
            if not build_time_str:
                try:
                    mtime = os.path.getmtime(__file__)
                    dt = datetime.datetime.fromtimestamp(mtime)
                    build_time_str = dt.strftime("%Y-%m-%d %H:%M:%S")
                except Exception:
                    build_time_str = "Unknown"

            # Optional version
            version = getattr(self, "app_version", None) or "1.0"
            lines = [
                f"Timeline Editor",
                f"Version: {version}",
                f"Build Time: {build_time_str} ({build_source})",
                "",
                "All rights reserved. This program is copyright and owned by Nanuvation.",
                "Do not replicate or distribute without written permission.",
            ]
            msg = "\n".join(lines)
            try:
                messagebox.showinfo("About", msg)
            except Exception:
                # Fallback minimal dialog
                top = tk.Toplevel(self.root)
                top.title("About")
                ttk.Label(top, text=msg).pack(padx=12, pady=12)
                ttk.Button(top, text="Close", command=top.destroy).pack(pady=(0,10))
        except Exception:
            pass

    def _zoom_fit(self):
        """Zoom out to fit the full timeline/audio in view."""
        canvas_width = self.canvas.winfo_width()
        if canvas_width <= 0:
            return
        max_time = max(
            self.audio_duration if self.audio_data else 0,
            max((evt.get("t", 0) for evt in self.timeline_data), default=0) if self.timeline_data else 0
        )
        if max_time <= 0:
            self.zoom_level = 100
        else:
            # Leave a small margin so the line is visible
            usable_width = max(50, canvas_width - 60)
            new_zoom = usable_width / max_time
            new_zoom = max(0.5, min(400, new_zoom))
            self.zoom_level = new_zoom
        self.waveform_cached = False
        # Scroll to start
        self.canvas.xview_moveto(0)
        self._update_canvas_view()
    
    def _update_universe(self):
        """Update selected universe and debounce monitor refresh (no layout rebuild)."""
        try:
            self.selected_universe = int(self.universe_var.get())
        except Exception:
            self.selected_universe = 1
            self.universe_var.set("1")
        # Debounce updates briefly to avoid stutter on change
        try:
            import time as _t
            self._monitor_debounce_until = _t.time() + 0.5
        except Exception:
            self._monitor_debounce_until = None
        # Clear last values so next loop refreshes labels without layout rebuild
        self._last_dmx_values = {}
    
    def _on_canvas_click(self, event):
        """Handle canvas click to select frame or seek playhead."""
        # Don't process click if we're dragging
        if self.is_dragging:
            return
        
        # Convert event coordinates to canvas coordinates
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        
        # Check if clicking near the playhead line (within 10 pixels)
        playhead_x = self.playhead_pos * self.zoom_level
        if abs(canvas_x - playhead_x) <= 10:
            self.dragging_playhead = True
            self.canvas.config(cursor="sb_h_double_arrow")
            return

        # Check if clicking near loop handles to start dragging them
        if self.loop_enabled and self.loop_end > self.loop_start:
            loop_start_x = self.loop_start * self.zoom_level
            loop_end_x = self.loop_end * self.zoom_level
            # Dragging loop in
            if abs(canvas_x - loop_start_x) <= 8:
                self._dragging_loop_in = True
                try:
                    self.canvas.config(cursor="sb_h_double_arrow")
                except Exception:
                    pass
                return
            # Dragging loop out
            if abs(canvas_x - loop_end_x) <= 8:
                self._dragging_loop_out = True
                try:
                    self.canvas.config(cursor="sb_h_double_arrow")
                except Exception:
                    pass
                return
        
        # Check if clicking on a marker (within 10 pixels)
        if self.markers:
            for marker in self.markers:
                marker_x = marker["t"] * self.zoom_level
                if abs(canvas_x - marker_x) <= 10:
                    # Jump playhead to marker
                    self.playhead_pos = marker["t"]
                    self.waveform_cached = False
                    self._update_canvas_view()
                    return
        
        # Check if clicking on a MIDI marker
        if hasattr(self, 'midi_marker_boxes') and self.midi_marker_boxes:
            for idx, (x1, y1, x2, y2) in self.midi_marker_boxes.items():
                if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                    # MIDI marker clicked - select it and jump playhead
                    self.selected_midi_marker = idx
                    self.playhead_pos = self.midi_markers[idx]["t"]
                    self.selected_frame = None
                    self.selected_session = None
                    # Prepare for dragging horizontally: keep initial offset
                    try:
                        marker_t = float(self.midi_markers[idx]["t"]) if self.midi_markers[idx] else 0.0
                    except Exception:
                        marker_t = 0.0
                    self._midi_drag_dt = (canvas_x / self.zoom_level) - marker_t
                    self.drag_midi_index = idx
                    self._drag_midi_ref = self.midi_markers[idx]
                    try:
                        self.canvas.config(cursor="fleur")
                    except Exception:
                        pass
                    self.waveform_cached = False
                    self._update_canvas_view()
                    return

        # Check if clicking on an OSC marker
        if hasattr(self, 'osc_marker_boxes') and self.osc_marker_boxes:
            for idx, (x1, y1, x2, y2) in self.osc_marker_boxes.items():
                if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                    # OSC marker clicked - select it and jump playhead
                    self.selected_osc_marker = idx
                    try:
                        marker_t = float(self.osc_markers[idx].get("t", 0.0)) if self.osc_markers[idx] else 0.0
                    except Exception:
                        marker_t = 0.0
                    self.playhead_pos = marker_t
                    # Prepare for dragging horizontally
                    self._osc_drag_dt = (canvas_x / self.zoom_level) - marker_t
                    self.drag_osc_index = idx
                    self._drag_osc_ref = self.osc_markers[idx]
                    try:
                        self.canvas.config(cursor="fleur")
                    except Exception:
                        pass
                    self.selected_frame = None
                    self.selected_session = None
                    self.waveform_cached = False
                    self._update_canvas_view()
                    return
        
        # Check if clicking on a session box
        if self.timeline_data and getattr(self, "session_bounds", {}):
            for s_id, (x1, x2, y1, y2) in self.session_bounds.items():
                if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                    # Start session drag to shift all frames (horizontal only)
                    self.selected_session = s_id
                    self.selected_frame = None
                    self._dragging_session_id = s_id
                    self._session_drag_start_x = canvas_x
                    # Snapshot original times for this session for incremental dragging
                    try:
                        self._session_times_snapshot = [e.get('t', 0.0) for e in self.timeline_data if e.get('session', 1) == s_id]
                    except Exception:
                        self._session_times_snapshot = None
                    try:
                        self.canvas.config(cursor="sb_h_double_arrow")
                    except Exception:
                        pass
                    return
            # Debug: Log click coordinates and bounds if no hit
            print(f"DEBUG Click at ({canvas_x}, {canvas_y})")
            for s_id, (x1, x2, y1, y2) in self.session_bounds.items():
                print(f"  Session {s_id}: x[{x1}, {x2}], y[{y1}, {y2}] - Hit: {x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2}")

        # Check if clicking on a frame
        if self.timeline_data and self.frame_boxes:
            for frame_idx, (x1, y1, x2, y2) in self.frame_boxes.items():
                if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                    # Frame clicked - select it
                    self.selected_frame = frame_idx
                    self.selected_session = None
                    self._update_canvas_view()
                    return
        
        # Not clicking on frame/marker - seek playhead
        self.playhead_pos = canvas_x / self.zoom_level
        self.selected_frame = None
        self.selected_session = None
        self._update_canvas_view()
    
    def _on_canvas_double_click(self, event):
        """Handle double-click to select entire session or open frame editor."""
        # Convert event coordinates to canvas coordinates
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        
        # Check if double-clicking on a MIDI marker - open editor
        if hasattr(self, 'midi_marker_boxes') and self.midi_marker_boxes:
            for idx, (x1, y1, x2, y2) in self.midi_marker_boxes.items():
                if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                    # Set playhead to marker and open editor
                    self.playhead_pos = self.midi_markers[idx]["t"]
                    self._edit_midi_marker()
                    return

        # Check if double-clicking on an OSC marker - open editor
        if hasattr(self, 'osc_marker_boxes') and self.osc_marker_boxes:
            for idx, (x1, y1, x2, y2) in self.osc_marker_boxes.items():
                if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                    self.playhead_pos = float(self.osc_markers[idx].get("t", 0.0))
                    self._edit_osc_marker(idx)
                    return
        
        # Check if double-clicking on a session box (Art-Net session)
        if self.timeline_data and getattr(self, "session_bounds", {}):
            for s_id, (x1, x2, y1, y2) in self.session_bounds.items():
                if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                    # Select entire session
                    self.selected_session = s_id
                    self.selected_frame = None
                    self._update_canvas_view()
                    return
        
        # Check if double-clicking on a frame
        if self.timeline_data and self.frame_boxes:
            for frame_idx, (x1, y1, x2, y2) in self.frame_boxes.items():
                if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                    # Open frame editor dialog
                    self._open_frame_editor(frame_idx)
                    return
    
    def _open_frame_editor(self, frame_idx):
        """Open a popup window to view and edit frame data."""
        if not (0 <= frame_idx < len(self.timeline_data)):
            return
        
        frame = self.timeline_data[frame_idx]
        
        # Create dialog window
        dialog = tk.Toplevel(self.root)
        dialog.title(f"Edit Frame {frame_idx}")
        dialog.geometry("500x400")
        dialog.resizable(True, True)
        
        # Frame info
        frame_info = tk.Frame(dialog, bg="gray20")
        frame_info.pack(fill=tk.BOTH, expand=False, padx=10, pady=10)
        
        tk.Label(frame_info, text=f"Frame Index: {frame_idx}", bg="gray20", fg="white").pack(anchor="w")
        tk.Label(frame_info, text=f"Time: {self._format_time(frame.get('t', 0))}", bg="gray20", fg="white").pack(anchor="w")
        tk.Label(frame_info, text=f"Universe: {frame.get('universe', 0)}", bg="gray20", fg="white").pack(anchor="w")
        tk.Label(frame_info, text=f"Opcode: {frame.get('opcode', 80)}", bg="gray20", fg="white").pack(anchor="w")
        
        # Editable fields
        edit_frame = tk.Frame(dialog, bg="gray30")
        edit_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Time field
        tk.Label(edit_frame, text="Time (seconds):", bg="gray30", fg="white").pack(anchor="w")
        time_var = tk.DoubleVar(value=frame.get('t', 0))
        time_entry = tk.Entry(edit_frame, textvariable=time_var, bg="gray40", fg="white", width=20)
        time_entry.pack(anchor="w", pady=5)
        
        # Universe field
        tk.Label(edit_frame, text="Universe:", bg="gray30", fg="white").pack(anchor="w")
        universe_var = tk.IntVar(value=frame.get('universe', 0))
        universe_entry = tk.Entry(edit_frame, textvariable=universe_var, bg="gray40", fg="white", width=20)
        universe_entry.pack(anchor="w", pady=5)
        
        # Opcode field
        tk.Label(edit_frame, text="Opcode:", bg="gray30", fg="white").pack(anchor="w")
        opcode_var = tk.IntVar(value=frame.get('opcode', 80))
        opcode_entry = tk.Entry(edit_frame, textvariable=opcode_var, bg="gray40", fg="white", width=20)
        opcode_entry.pack(anchor="w", pady=5)
        
        # Payload preview (read-only)
        tk.Label(edit_frame, text="Art-Net Payload (preview):", bg="gray30", fg="white").pack(anchor="w", pady=(10, 5))
        payload_text = tk.Text(edit_frame, bg="gray40", fg="cyan", height=8, width=60, wrap=tk.WORD)
        payload_text.pack(fill=tk.BOTH, expand=True, pady=5)
        
        payload = frame.get('payload', '')
        if payload:
            # Show hex preview of first 64 bytes
            try:
                decoded = base64.b64decode(payload)
                hex_preview = ' '.join(f'{b:02x}' for b in decoded[:64])
                payload_text.insert(tk.END, f"Hex: {hex_preview}...\n\nLength: {len(decoded)} bytes")
            except:
                payload_text.insert(tk.END, f"Base64: {payload[:100]}...")
        payload_text.config(state=tk.DISABLED)
        
        # Button frame
        button_frame = tk.Frame(dialog, bg="gray20")
        button_frame.pack(fill=tk.X, padx=10, pady=10)
        
        def save_changes():
            try:
                frame['t'] = time_var.get()
                frame['universe'] = universe_var.get()
                frame['opcode'] = opcode_var.get()
                self.waveform_cached = False
                self._update_canvas_view()
                messagebox.showinfo("Saved", "Frame updated successfully")
                dialog.destroy()
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save: {str(e)}")
        
        tk.Button(button_frame, text="Save", command=save_changes, bg="lime", fg="black", width=15).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Cancel", command=dialog.destroy, bg="orange", fg="black", width=15).pack(side=tk.LEFT, padx=5)
    
    def _on_canvas_right_click(self, event):
        """Handle right-click to delete selected frame or session."""
        # Convert event coordinates to canvas coordinates
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)

        # Context menu for markers (OSC/MIDI)
        try:
            # Check OSC marker hit first
            if hasattr(self, 'osc_marker_boxes') and self.osc_marker_boxes:
                for idx, (x1, y1, x2, y2) in self.osc_marker_boxes.items():
                    if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                        self.selected_osc_marker = idx
                        menu = tk.Menu(self.root, tearoff=0)
                        menu.add_command(label="Edit OSC Marker", command=lambda i=idx: self._edit_osc_marker(i))
                        menu.add_command(label="Delete OSC Marker", command=lambda i=idx: self._delete_osc_marker(i))
                        try:
                            menu.tk_popup(self.root.winfo_pointerx(), self.root.winfo_pointery())
                        finally:
                            menu.grab_release()
                        return
            # Check MIDI marker hit
            if hasattr(self, 'midi_marker_boxes') and self.midi_marker_boxes:
                for idx, (x1, y1, x2, y2) in self.midi_marker_boxes.items():
                    if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                        self.selected_midi_marker = idx
                        menu = tk.Menu(self.root, tearoff=0)
                        menu.add_command(label="Edit MIDI Marker", command=self._edit_midi_marker)
                        menu.add_command(label="Delete MIDI Marker", command=lambda: self._delete_selected_midi_marker())
                        try:
                            menu.tk_popup(self.root.winfo_pointerx(), self.root.winfo_pointery())
                        finally:
                            menu.grab_release()
                        return
        except Exception:
            pass

        # If right-clicking on an OSC marker, delete it
        if hasattr(self, 'osc_marker_boxes') and self.osc_marker_boxes:
            for idx, (x1, y1, x2, y2) in self.osc_marker_boxes.items():
                if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                    if 0 <= idx < len(self.osc_markers):
                        try:
                            self._save_undo_state()
                        except Exception:
                            pass
                        self.osc_markers.pop(idx)
                        self.selected_osc_marker = None
                        self.waveform_cached = False
                        self._update_canvas_view()
                        return

        # Session context menu: edit name or delete session
        if self.timeline_data and getattr(self, "session_bounds", {}):
            for s_id, (x1, x2, y1, y2) in self.session_bounds.items():
                if x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2:
                    self.selected_session = s_id
                    menu = tk.Menu(self.root, tearoff=0)
                    menu.add_command(label="Edit Session Name", command=self._rename_session)
                    def _delete_session():
                        try:
                            self._save_undo_state()
                        except Exception:
                            pass
                        self.timeline_data = [e for e in self.timeline_data if e.get("session", 1) != s_id]
                        try:
                            if s_id in self.session_names:
                                del self.session_names[s_id]
                        except Exception:
                            pass
                        self.selected_session = None
                        self.selected_frame = None
                        self.waveform_cached = False
                        self._update_canvas_view()
                    menu.add_command(label="Delete Session", command=_delete_session)
                    try:
                        menu.tk_popup(self.root.winfo_pointerx(), self.root.winfo_pointery())
                    finally:
                        menu.grab_release()
                    return

    def _on_delete_key(self, event=None):
        """Handle Delete key to remove selected session, frame, or MIDI marker."""
        # Check if OSC marker is selected
        if self.selected_osc_marker is not None and 0 <= self.selected_osc_marker < len(self.osc_markers):
            try:
                self._save_undo_state()
            except Exception:
                pass
            self.osc_markers.pop(self.selected_osc_marker)
            self.selected_osc_marker = None
            self.waveform_cached = False
            self._update_canvas_view()
            return
        # Check if MIDI marker is selected
        if self.selected_midi_marker is not None and 0 <= self.selected_midi_marker < len(self.midi_markers):
            self._save_undo_state()
            self.midi_markers.pop(self.selected_midi_marker)
            self.selected_midi_marker = None
            self.waveform_cached = False
            self._update_canvas_view()
            return
        
        if self.timeline_data:
            if self.selected_session is not None:
                # Save undo state before deletion
                self._save_undo_state()
                s_id = self.selected_session
                self.timeline_data = [e for e in self.timeline_data if e.get("session", 1) != s_id]
                self.selected_session = None
                self.selected_frame = None
                self.waveform_cached = False
                self._update_canvas_view()
                return
            if self.selected_frame is not None and 0 <= self.selected_frame < len(self.timeline_data):
                # Save undo state before deletion
                self._save_undo_state()
                self.timeline_data.pop(self.selected_frame)
                self.selected_frame = None
                self.waveform_cached = False
                self._update_canvas_view()
        
        # Note: deletion via mouse position is handled in mouse event handlers.

    def _delete_osc_marker(self, idx: int):
        try:
            if 0 <= idx < len(self.osc_markers):
                self._save_undo_state()
                self.osc_markers.pop(idx)
                if self.selected_osc_marker == idx:
                    self.selected_osc_marker = None
                self.waveform_cached = False
                self._update_canvas_view()
        except Exception:
            pass

    def _delete_selected_midi_marker(self):
        try:
            if self.selected_midi_marker is not None and 0 <= self.selected_midi_marker < len(self.midi_markers):
                self._save_undo_state()
                self.midi_markers.pop(self.selected_midi_marker)
                self.selected_midi_marker = None
                self.waveform_cached = False
                self._update_canvas_view()
        except Exception:
            pass

    def _ensure_osc_tooltip(self):
        try:
            if getattr(self, '_osc_tooltip', None) is None:
                tip = tk.Toplevel(self.root)
                tip.overrideredirect(True)
                tip.withdraw()
                tip.configure(bg="#000000")
                lbl = tk.Label(tip, text="", bg="#000000", fg="#ffffff", font=("Arial", 8))
                lbl.pack(padx=6, pady=4)
                self._osc_tooltip = tip
                self._osc_tooltip_label = lbl
        except Exception:
            pass

    def _hide_osc_tooltip(self):
        try:
            if getattr(self, '_osc_tooltip', None):
                self._osc_tooltip.withdraw()
        except Exception:
            pass

    def _show_osc_tooltip(self, x: int, y: int, text: str):
        try:
            self._ensure_osc_tooltip()
            if getattr(self, '_osc_tooltip_label', None):
                self._osc_tooltip_label.config(text=text)
            if getattr(self, '_osc_tooltip', None):
                # Position near cursor
                self._osc_tooltip.geometry(f"+{x+12}+{y+12}")
                self._osc_tooltip.deiconify()
        except Exception:
            pass
    
    def _on_canvas_drag(self, event):
        """Handle canvas drag to create zoom selection box or drag playhead."""
        # Hide tooltip while dragging
        self._hide_osc_tooltip()
        # Handle playhead dragging
        if self.dragging_playhead:
            canvas_x = self.canvas.canvasx(event.x)
            self.playhead_pos = max(0, canvas_x / self.zoom_level)
            # Delete old playhead and redraw at new position without full canvas redraw
            self.canvas.delete("playhead")
            canvas_height = self.canvas.winfo_height()
            playhead_x = self.playhead_pos * self.zoom_level
            self.canvas.create_line(playhead_x, 0, playhead_x, canvas_height, fill="red", width=2, tags="playhead")
            self.playhead_label.config(text=self._format_time(self.playhead_pos))
            try:
                if hasattr(self, "monitor_timecode_label") and self.monitor_timecode_label:
                    self.monitor_timecode_label.config(text=self._format_time(self.playhead_pos))
            except Exception:
                pass
            return

        # Handle session dragging to shift all frames in that session
        if self._dragging_session_id is not None and self._session_drag_start_x is not None:
            try:
                cur_x = self.canvas.canvasx(event.x)
                delta_px = cur_x - float(self._session_drag_start_x)
                delta_t = delta_px / float(self.zoom_level if self.zoom_level else 1.0)
            except Exception:
                delta_t = 0.0
            # Apply delta to all frames in the session (non-destructive for others)
            try:
                sid = self._dragging_session_id
                idx = 0
                for e in self.timeline_data:
                    if e.get('session', 1) == sid:
                        try:
                            original_t = self._session_times_snapshot[idx] if self._session_times_snapshot and idx < len(self._session_times_snapshot) else e.get('t', 0.0)
                        except Exception:
                            original_t = e.get('t', 0.0)
                        new_t = max(0.0, float(original_t) + float(delta_t))
                        e['t'] = new_t
                        idx += 1
            except Exception:
                pass
            # Do not move playhead during session drag
            self.waveform_cached = False
            self._update_canvas_view()
            return

        # Handle loop handle dragging
        if getattr(self, "_dragging_loop_in", False) or getattr(self, "_dragging_loop_out", False):
            canvas_x = self.canvas.canvasx(event.x)
            new_t = max(0.0, canvas_x / self.zoom_level)
            # Snap to bounds: ensure loop_start < loop_end and maintain minimal width
            min_gap = 0.05
            try:
                if getattr(self, "_dragging_loop_in", False):
                    self.loop_start = min(new_t, self.loop_end - min_gap)
                else:
                    self.loop_end = max(new_t, self.loop_start + min_gap)
                self.loop_enabled = True
            except Exception:
                pass
            self.waveform_cached = False
            self._update_canvas_view()
            return

        # Handle MIDI marker dragging
        if self.drag_midi_index is not None and self._drag_midi_ref is not None:
            try:
                canvas_x = self.canvas.canvasx(event.x)
                new_t = max(0.0, (canvas_x / self.zoom_level) - float(self._midi_drag_dt))
            except Exception:
                new_t = max(0.0, self.playhead_pos)
            # Apply new time to the dragged marker
            try:
                self._drag_midi_ref["t"] = new_t
            except Exception:
                pass
            # Re-sort markers and update selected index to the dragged item
            try:
                ref = self._drag_midi_ref
                self.midi_markers.sort(key=lambda m: m.get("t", 0.0))
                self.selected_midi_marker = self.midi_markers.index(ref)
            except Exception:
                pass
            # Keep playhead aligned with dragged marker start for feedback
            self.playhead_pos = new_t
            self.waveform_cached = False
            self._update_canvas_view()
            return

        # Handle OSC marker dragging
        if self.drag_osc_index is not None and self._drag_osc_ref is not None:
            try:
                canvas_x = self.canvas.canvasx(event.x)
                new_t = max(0.0, (canvas_x / self.zoom_level) - float(self._osc_drag_dt))
            except Exception:
                new_t = max(0.0, self.playhead_pos)
            try:
                self._drag_osc_ref["t"] = new_t
            except Exception:
                pass
            try:
                ref = self._drag_osc_ref
                self.osc_markers.sort(key=lambda m: m.get("t", 0.0))
                self.selected_osc_marker = self.osc_markers.index(ref)
            except Exception:
                pass
            self.playhead_pos = new_t
            self.waveform_cached = False
            self._update_canvas_view()
            return
        
        # Initialize drag tracking on first motion
        if self.drag_start is None:
            self.drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
            self.is_dragging = False
            return
        
        # Check if we've moved enough to be considered a drag
        start_x, start_y = self.drag_start
        cur_x, cur_y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        distance = ((cur_x - start_x)**2 + (cur_y - start_y)**2)**0.5
        
        if not self.is_dragging and distance < self.drag_threshold_distance:
            return  # Not enough movement yet
        
        self.is_dragging = True
        
        # Delete previous zoom box if exists
        if self.zoom_box_id is not None:
            self.canvas.delete(self.zoom_box_id)
        
        # Draw zoom selection box
        self.zoom_box_id = self.canvas.create_rectangle(
            start_x, start_y, cur_x, cur_y,
            outline="yellow", width=2, dash=(4, 4)
        )
    
    def _on_canvas_release(self, event):
        """Handle mouse release to zoom into selected area or stop playhead dragging."""
        # Hide tooltip on release
        self._hide_osc_tooltip()
        # Stop playhead dragging
        if self.dragging_playhead:
            self.dragging_playhead = False
            try:
                self.canvas.config(cursor="crosshair")
            except Exception:
                pass
            return
        # Finish session drag
        if self._dragging_session_id is not None:
            sid = self._dragging_session_id
            self._dragging_session_id = None
            self._session_drag_start_x = None
            self._session_times_snapshot = None
            try:
                self.canvas.config(cursor="crosshair")
            except Exception:
                pass
            # Save undo state after the shift
            try:
                self._save_undo_state()
            except Exception:
                pass
            self.waveform_cached = False
            self._update_canvas_view()
            # Do not treat as zoom selection
            self.drag_start = None
            self.is_dragging = False
            return

        # Stop loop handle dragging
        if getattr(self, "_dragging_loop_in", False) or getattr(self, "_dragging_loop_out", False):
            self._dragging_loop_in = False
            self._dragging_loop_out = False
            try:
                self.canvas.config(cursor="crosshair")
            except Exception:
                pass
            # Redraw to finalize positions
            self.waveform_cached = False
            self._update_canvas_view()
            return

        # Stop MIDI marker dragging
        if self.drag_midi_index is not None:
            try:
                self.canvas.config(cursor="crosshair")
            except Exception:
                pass
            # Commit final sort and selection
            try:
                ref = self._drag_midi_ref
                self.midi_markers.sort(key=lambda m: m.get("t", 0.0))
                if ref in self.midi_markers:
                    self.selected_midi_marker = self.midi_markers.index(ref)
            except Exception:
                pass
            # Clear drag state
            self.drag_midi_index = None
            self._drag_midi_ref = None
            self._midi_drag_dt = 0.0
            self.waveform_cached = False
            self._update_canvas_view()
            # Do not treat as zoom selection
            self.drag_start = None
            self.is_dragging = False
            return

        # Stop OSC marker dragging
        if self.drag_osc_index is not None:
            try:
                self.canvas.config(cursor="crosshair")
            except Exception:
                pass
            try:
                ref = self._drag_osc_ref
                self.osc_markers.sort(key=lambda m: m.get("t", 0.0))
                if ref in self.osc_markers:
                    self.selected_osc_marker = self.osc_markers.index(ref)
            except Exception:
                pass
            self.drag_osc_index = None
            self._drag_osc_ref = None
            self._osc_drag_dt = 0.0
            self.waveform_cached = False
            self._update_canvas_view()
            self.drag_start = None
            self.is_dragging = False
            return
        
        if self.drag_start is None:
            return
        
        # Clean up zoom box
        if self.zoom_box_id is not None:
            self.canvas.delete(self.zoom_box_id)
            self.zoom_box_id = None
        
        # If it wasn't a real drag (too small), treat as a click
        if not self.is_dragging:
            self.drag_start = None
            self.is_dragging = False
            # Let the click be processed normally
            return
        
        start_x, start_y = self.drag_start
        self.drag_start = None
        self.is_dragging = False
        
        # Get canvas coordinates
        start_canvas_x = start_x
        end_canvas_x = self.canvas.canvasx(event.x)
        
        # Ensure correct order
        min_x = min(start_canvas_x, end_canvas_x)
        max_x = max(start_canvas_x, end_canvas_x)
        
        # Check if drag was significant enough (at least 10 pixels)
        if abs(max_x - min_x) < 10:
            return  # Too small, ignore
        
        # Convert canvas coordinates to time
        min_time = min_x / self.zoom_level
        max_time = max_x / self.zoom_level
        
        if max_time <= min_time:
            return
        
        # Calculate new zoom level to fit selected area in view
        canvas_width = self.canvas.winfo_width()
        new_zoom = canvas_width / (max_time - min_time)
        
        # Limit zoom to reasonable range (0.5x to 400x) for closer views
        new_zoom = max(0.5, min(400, new_zoom))
        self.zoom_level = new_zoom
        
        # Set playhead to start of selection
        self.playhead_pos = min_time
        
        # Force redraw with new zoom
        self.waveform_cached = False
        self._update_canvas_view()
        
        # Scroll to bring the selection into view (centered on selection start)
        max_time_total = max(
            self.audio_duration if self.audio_data else 0,
            max((evt.get("t", 0) for evt in self.timeline_data), default=0) if self.timeline_data else 0
        )
        total_width = int(max_time_total * self.zoom_level) + 100 if max_time_total > 0 else canvas_width
        canvas_visible = self.canvas.winfo_width()
        target_x = min_time * self.zoom_level
        if total_width > canvas_visible:
            target_scroll = max(0, min(1.0, (target_x - canvas_visible / 3) / (total_width - canvas_visible)))
            self.canvas.xview_moveto(target_scroll)
    
    def _update_canvas_view(self):
        """Redraw the timeline canvas with audio waveform, events, and playhead."""
        # During playback/recording, only update playhead position (fast update)
        if (self.is_playing or self.recording) and self.waveform_cached:
            # Delete only the playhead from previous frame and redraw it
            self.canvas.delete("playhead")
            
            canvas_height = self.canvas.winfo_height()
            canvas_width = self.canvas.winfo_width()
            
            playhead_x = self.playhead_pos * self.zoom_level
            
            # Draw playhead
            self.canvas.create_line(playhead_x, 0, playhead_x, canvas_height, fill="red", width=2, tags="playhead")
            
            # Auto-scroll to follow playhead
            max_time = max(
                self.audio_duration if self.audio_data else 0,
                max((evt.get("t", 0) for evt in self.timeline_data), default=0) if self.timeline_data else 0
            )
            total_width = int(max_time * self.zoom_level) + 100
            
            if total_width > canvas_width:
                target_scroll = max(0, min(1.0, (playhead_x - canvas_width / 3) / (total_width - canvas_width)))
                self.canvas.xview_moveto(target_scroll)
            
            self.playhead_label.config(text=self._format_time(self.playhead_pos))
            try:
                if hasattr(self, "monitor_timecode_label") and self.monitor_timecode_label:
                    self.monitor_timecode_label.config(text=self._format_time(self.playhead_pos))
            except Exception:
                pass
            return
        
        # Full redraw when stopped or first load
        self.canvas.delete("all")
        
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        
        max_time = max(
            self.audio_duration if self.audio_data else 0,
            max((evt.get("t", 0) for evt in self.timeline_data), default=0) if self.timeline_data else 0
        )
        
        if max_time == 0:
            self.canvas.create_text(50, 20, text="No audio or timeline loaded", fill="white", anchor="nw")
            return
        
        # Auto-scroll to follow playhead when playing/recording
        if self.is_playing or self.recording:
            playhead_x = self.playhead_pos * self.zoom_level
            canvas_visible_width = canvas_width
            
            # Calculate total scrollable width
            total_width = int(max_time * self.zoom_level) + 100
            
            # If playhead is visible, keep scrolling to follow it
            # Center the playhead in the view
            if total_width > canvas_visible_width:
                target_scroll = max(0, min(1.0, (playhead_x - canvas_visible_width / 3) / (total_width - canvas_visible_width)))
                self.canvas.xview_moveto(target_scroll)
        
        self.duration_label.config(text=self._format_time(max_time))
        self.playhead_label.config(text=self._format_time(self.playhead_pos))
        try:
            if hasattr(self, "monitor_timecode_label") and self.monitor_timecode_label:
                self.monitor_timecode_label.config(text=self._format_time(self.playhead_pos))
        except Exception:
            pass
        self.events_label.config(text=str(len(self.timeline_data) if self.timeline_data else 0))
        
        # Update loop status indicator
        if self.loop_enabled and self.loop_end > self.loop_start:
            loop_text = f"🔁 LOOP: {self._format_time(self.loop_start)} - {self._format_time(self.loop_end)}"
            self.loop_label.config(text=loop_text, foreground="lime")
        else:
            self.loop_label.config(text="")
        
        if self.audio_data:
            self._draw_waveform(canvas_width, canvas_height, max_time)
        
        # Calculate grid and set scroll region first
        max_x = int(max_time * self.zoom_level) + 100
        self.canvas.config(scrollregion=(0, 0, max_x, canvas_height))
        
        for i in range(0, int(max_time) + 2):
            x = i * self.zoom_level
            if x > max_x:
                break
            self.canvas.create_line(x, 0, x, canvas_height, fill="gray20", dash=(4, 4))
            self.canvas.create_text(x + 5, 5, text=f"{i}s", fill="gray50", anchor="nw", font=("mono", 8))
        
        if self.timeline_data:
            # Position sessions and universes just below the waveform area
            waveform_height = min(100, canvas_height // 3) if self.audio_data else 0
            waveform_y_top = 30
            waveform_y_bottom = waveform_y_top + waveform_height
            base_y = waveform_y_bottom + 50  # increased gap below waveform to make room for session names
            row_spacing = 24
            session_gap = 24
            
            # First pass: gather sessions and universes per session preserving order
            session_order = []
            session_universes = {}
            palette = ["cyan", "magenta", "yellow", "orange", "lime", "deeppink", "deepskyblue", "violet"]
            for evt in self.timeline_data:
                s_id = evt.get("session", 1)
                universe = evt.get("universe", 0)
                if s_id not in session_universes:
                    session_universes[s_id] = []
                    session_order.append(s_id)
                if universe not in session_universes[s_id]:
                    session_universes[s_id].append(universe)
            
            # Compute session base rows
            session_rows = {}
            current_y = base_y
            for s_id in session_order:
                session_rows[s_id] = current_y
                current_y += len(session_universes[s_id]) * row_spacing + session_gap + 35  # extra pixels for session name spacing and separation

            # Precompute universe row index per session
            session_universe_index = {
                s_id: {u: idx for idx, u in enumerate(session_universes[s_id])}
                for s_id in session_order
            }
            
            # Track session bounds for box drawing
            session_bounds = {s_id: [float('inf'), float('-inf'), float('inf'), float('-inf')] for s_id in session_order}
            
            self.frame_boxes = {}  # Reset frame boxes for selection tracking
            max_y_drawn = canvas_height
            
            for frame_idx, evt in enumerate(self.timeline_data):
                universe = evt.get("universe", 0)
                opcode = evt.get("opcode", 80)
                time_val = evt.get("t", 0)
                session_id = evt.get("session", 1)
                x = time_val * self.zoom_level
                
                # Row within this session
                universe_idx_map = session_universe_index.get(session_id, {})
                row_idx = universe_idx_map.get(universe, 0)
                y = session_rows.get(session_id, base_y) + row_idx * row_spacing
                
                # Colors
                base_color = palette[row_idx % len(palette)]
                session_color = self.session_palette[(session_id - 1) % len(self.session_palette)] if hasattr(self, "session_palette") else base_color
                color = session_color if opcode == 80 else "orange"
                
                # Determine if this frame is selected
                is_selected = (self.selected_frame == frame_idx)
                
                # Draw frame block (larger for better clickability)
                block_width = max(8, self.zoom_level // 10)
                block_height = 14
                outline_color = "white" if is_selected else session_color
                self.canvas.create_rectangle(
                    x - block_width, y - block_height, x + block_width, y + block_height,
                    fill=color, outline=outline_color, width=2 if is_selected else 1, tags=f"frame_{frame_idx}"
                )
                
                # Universe/session label at right side for clarity - moved to avoid overlapping session name
                label_y = y
                self.canvas.create_text(self.canvas.winfo_width() - 100, label_y, text=f"U{universe} S{session_id}", fill=session_color, anchor="e", font=("mono", 8))
                
                self.frame_boxes[frame_idx] = (x - block_width, y - block_height, x + block_width, y + block_height)
                
                # Update bounds for session box
                b = session_bounds[session_id]
                b[0] = min(b[0], x - block_width)
                b[1] = max(b[1], x + block_width)
                b[2] = min(b[2], y - block_height)
                b[3] = max(b[3], y + block_height)
                max_y_drawn = max(max_y_drawn, y + block_height)
            
            # Draw session bounding boxes
            padding = 10
            for s_id in session_order:
                b = session_bounds[s_id]
                if b[0] == float('inf'):
                    continue
                session_color = self.session_palette[(s_id - 1) % len(self.session_palette)] if hasattr(self, "session_palette") else "gray"
                outline_width = 3 if self.selected_session == s_id else 2
                dash_style = () if self.selected_session == s_id else (6, 4)
                self.canvas.create_rectangle(
                    b[0] - padding, b[2] - padding, b[1] + padding, b[3] + padding,
                    outline=session_color, dash=dash_style, width=outline_width
                )
                # Use custom name if available - position ABOVE the box for visibility
                session_label = self.session_names.get(s_id, f"Session {s_id}")
                # Place label above the box so it doesn't overlap with Art-Net data
                label_x = max(b[0] - padding + 5, 5)  # Keep at least 5 pixels from left edge
                label_y = b[2] - padding - 12  # Position above the top border of the box
                self.canvas.create_text(label_x, label_y, text=session_label,
                                        fill=session_color, anchor="sw", font=("mono", 9, "bold"))
            
            # Extend scrollregion height if needed
            if max_y_drawn + 80 > int(self.canvas.cget('height')):
                self.canvas.config(scrollregion=(0, 0, max_x, max_y_drawn + 100))

            # Store padded bounds for click selection
            self.session_bounds = {
                s_id: (b[0] - padding, b[1] + padding, b[2] - padding, b[3] + padding)
                for s_id, b in session_bounds.items() if b[0] != float('inf')
            }
        
        # Draw loop region
        if self.loop_enabled and self.loop_end > self.loop_start:
            loop_start_x = self.loop_start * self.zoom_level
            loop_end_x = self.loop_end * self.zoom_level
            # Draw semi-transparent green region
            self.canvas.create_rectangle(
                loop_start_x, 0, loop_end_x, canvas_height,
                fill="green", stipple="gray25", outline=""
            )
            # Draw loop boundaries
            self.canvas.create_line(loop_start_x, 0, loop_start_x, canvas_height, fill="lime", width=3, tags=("loop_in_handle", "loop_handle"))
            self.canvas.create_line(loop_end_x, 0, loop_end_x, canvas_height, fill="lime", width=3, tags=("loop_out_handle", "loop_handle"))
            # Draw loop labels
            self.canvas.create_text(loop_start_x + 5, canvas_height - 20, text="LOOP IN", fill="lime", anchor="w", font=("Arial", 9, "bold"))
            self.canvas.create_text(loop_end_x - 5, canvas_height - 20, text="LOOP OUT", fill="lime", anchor="e", font=("Arial", 9, "bold"))
        
        # Draw markers
        if self.markers:
            for marker in self.markers:
                marker_x = marker["t"] * self.zoom_level
                marker_label = marker["label"]
                # Draw marker line
                self.canvas.create_line(marker_x, 0, marker_x, canvas_height, fill="yellow", width=2, dash=(4, 4))
                # Draw marker label at top
                self.canvas.create_text(marker_x + 3, 5, text=marker_label, fill="yellow", anchor="nw", font=("Arial", 8, "bold"))
        
        # Draw MIDI markers section
        # Draw OSC markers section (above MIDI)
        if self.osc_markers:
            osc_section_height = 80
            # Place OSC section just above MIDI section when MIDI exists, otherwise at bottom
            has_midi = bool(self.midi_markers)
            base_bottom_margin = 10
            midi_section_height = 60 if has_midi else 0
            inter_lane_gap = 48 if has_midi else 0  # base extra space so lanes aren't touching
            # Dynamically increase gap if lane titles would overlap
            # Estimate label heights and positions similar to where we draw them (top - 22)
            if has_midi:
                tentative_osc_bottom = canvas_height - (midi_section_height + base_bottom_margin + inter_lane_gap)
                tentative_osc_top = tentative_osc_bottom - osc_section_height
                tentative_midi_top = canvas_height - midi_section_height - base_bottom_margin
                osc_label_y = tentative_osc_top - 22
                midi_label_y = tentative_midi_top - 22
                est_label_h = 16
                osc_label_bottom = osc_label_y + est_label_h
                midi_label_top = midi_label_y
                if osc_label_bottom >= midi_label_top:
                    inter_lane_gap += 40  # add more room to prevent overlap
            osc_section_bottom = canvas_height - (midi_section_height + base_bottom_margin + inter_lane_gap)
            osc_section_top = osc_section_bottom - osc_section_height
            osc_section_center = (osc_section_top + osc_section_bottom) / 2

            # Draw section background and label: place label ABOVE the lane like Art-Net sessions
            left_padding = 14
            self.canvas.create_rectangle(0, osc_section_top, max_x, osc_section_bottom,
                                        fill="#111111", outline="deepskyblue", width=2)
            self.canvas.create_text(left_padding, osc_section_top - 22, text="OSC Markers",
                                   fill="deepskyblue", anchor="nw", font=("Arial", 9, "bold"))

            # Track OSC marker bounds for click selection
            self.osc_marker_boxes = {}
            # Track placed label boxes to avoid overlap
            placed_osc_labels = []  # list of (x1,y1,x2,y2)

            for idx, osc in enumerate(self.osc_markers):
                marker_x = osc.get("t", 0.0) * self.zoom_level
                name = osc.get("name", "OSC")
                address = osc.get("address", "/")
                # Draw a fixed-size block (match MIDI marker height/visual size)
                block_width = 20
                block_height = 20
                is_selected = (self.selected_osc_marker == idx)
                outline_color = "white" if is_selected else "deepskyblue"
                fill_color = "dodgerblue" if is_selected else "steelblue"
                self.canvas.create_rectangle(
                    marker_x - 2, osc_section_center - block_height,
                    marker_x + block_width, osc_section_center + block_height,
                    fill=fill_color, outline=outline_color, width=2 if is_selected else 1,
                    tags=f"osc_{idx}"
                )
                # Vertical line
                self.canvas.create_line(marker_x, osc_section_top, marker_x, osc_section_bottom,
                                       fill="deepskyblue", width=2, dash=(2, 2))
                # Label with name (stagger + collision flip)
                info = name if name else "OSC"
                # Basic truncation to avoid extremely long overflow
                max_label_chars = 18
                if len(info) > max_label_chars:
                    info = info[:max_label_chars-1] + "…"
                # Alternating baseline: even below, odd above
                below = (idx % 2 == 0)
                label_y = osc_section_center + (block_height + 10 if below else -(block_height + 10))
                label_x = marker_x
                # Compute tentative bounding box (approximate width)
                # Assume ~7px per char at this font size
                est_w = max(20, 7 * len(info))
                est_h = 12
                def overlaps(x1,y1,x2,y2, boxes):
                    for (ax1,ay1,ax2,ay2) in boxes:
                        if not (x2 < ax1 or x1 > ax2 or y2 < ay1 or y1 > ay2):
                            return True
                    return False
                # Try flip if overlapping
                x1 = label_x
                y1 = label_y - est_h
                x2 = label_x + est_w
                y2 = label_y
                if overlaps(x1,y1,x2,y2, placed_osc_labels):
                    below = not below
                    label_y = osc_section_center + (block_height + 10 if below else -(block_height + 10))
                    y1 = label_y - est_h
                    y2 = label_y
                # Final small vertical nudge if still overlapping
                if overlaps(x1,y1,x2,y2, placed_osc_labels):
                    label_y += (10 if below else -10)
                    y1 = label_y - est_h
                    y2 = label_y
                self.canvas.create_text(label_x, label_y, text=info,
                                       fill="white", anchor="w", font=("Arial", 7, "bold"))
                placed_osc_labels.append((label_x, y1, x2, y2))
                self.osc_marker_boxes[idx] = (
                    marker_x - 2, osc_section_center - block_height,
                    marker_x + block_width, osc_section_center + block_height
                )
        else:
            self.osc_marker_boxes = {}

        # Draw MIDI markers section
        if self.midi_markers:
            # Position MIDI section at bottom of canvas
            midi_section_height = 80
            midi_section_top = canvas_height - midi_section_height - 10
            midi_section_bottom = canvas_height - 10
            midi_section_center = (midi_section_top + midi_section_bottom) / 2
            
            # Draw section background and label: place label ABOVE the lane like Art-Net sessions
            left_padding = 14
            self.canvas.create_rectangle(0, midi_section_top, max_x, midi_section_bottom,
                                        fill="gray15", outline="purple", width=2)
            self.canvas.create_text(left_padding, midi_section_top - 22, text="MIDI Markers", 
                                   fill="purple", anchor="nw", font=("Arial", 9, "bold"))
            
            # Track MIDI marker bounds for click selection
            self.midi_marker_boxes = {}
            placed_midi_labels = []
            
            # Draw each MIDI marker
            for idx, midi_marker in enumerate(self.midi_markers):
                marker_x = midi_marker["t"] * self.zoom_level
                note = midi_marker["note"]
                velocity = midi_marker["velocity"]
                channel = midi_marker["channel"]
                duration = midi_marker.get("duration", 0.1)
                label = midi_marker.get("label", "")
                
                # Draw marker block showing duration
                duration_width = max(8, duration * self.zoom_level)
                block_height = 20
                
                # Determine if this marker is selected
                is_selected = (self.selected_midi_marker == idx)
                outline_color = "white" if is_selected else "purple"
                fill_color = "magenta" if is_selected else "mediumpurple"
                
                # Draw block
                self.canvas.create_rectangle(
                    marker_x - 2, midi_section_center - block_height, 
                    marker_x + duration_width, midi_section_center + block_height,
                    fill=fill_color, outline=outline_color, width=2 if is_selected else 1,
                    tags=f"midi_{idx}"
                )
                
                # Draw vertical marker line
                self.canvas.create_line(marker_x, midi_section_top, marker_x, midi_section_bottom,
                                       fill="purple", width=2, dash=(2, 2))
                
                # Label with MIDI info (stagger + collision flip)
                info_text = f"N{note}"
                if label:
                    info_text = f"{label} ({info_text})"
                max_label_chars = 18
                if len(info_text) > max_label_chars:
                    info_text = info_text[:max_label_chars-1] + "…"
                below = (idx % 2 == 0)
                label_y = midi_section_center + (block_height + 10 if below else -(block_height + 10))
                label_x = marker_x
                est_w = max(20, 7 * len(info_text))
                est_h = 12
                def overlaps_m(x1,y1,x2,y2):
                    for (ax1,ay1,ax2,ay2) in placed_midi_labels:
                        if not (x2 < ax1 or x1 > ax2 or y2 < ay1 or y1 > ay2):
                            return True
                    return False
                x1 = label_x
                y1 = label_y - est_h
                x2 = label_x + est_w
                y2 = label_y
                if overlaps_m(x1,y1,x2,y2):
                    below = not below
                    label_y = midi_section_center + (block_height + 10 if below else -(block_height + 10))
                    y1 = label_y - est_h
                    y2 = label_y
                if overlaps_m(x1,y1,x2,y2):
                    label_y += (10 if below else -10)
                    y1 = label_y - est_h
                    y2 = label_y
                self.canvas.create_text(label_x, label_y, text=info_text,
                                       fill="white", anchor="w", font=("Arial", 7, "bold"))
                placed_midi_labels.append((label_x, y1, x2, y2))
                
                # Store bounds for click detection
                self.midi_marker_boxes[idx] = (
                    marker_x - 2, midi_section_center - block_height,
                    marker_x + duration_width, midi_section_center + block_height
                )
        else:
            # Initialize empty if no MIDI markers
            self.midi_marker_boxes = {}

            # Tooltip on hover for OSC markers
            def _maybe_show_osc_tooltip(event=None):
                try:
                    cx = self.canvas.canvasx(event.x)
                    cy = self.canvas.canvasy(event.y)
                    if hasattr(self, 'osc_marker_boxes') and self.osc_marker_boxes:
                        for idx, (x1, y1, x2, y2) in self.osc_marker_boxes.items():
                            if x1 <= cx <= x2 and y1 <= cy <= y2 and 0 <= idx < len(self.osc_markers):
                                m = self.osc_markers[idx]
                                txt = f"{m.get('name','OSC')}\n{m.get('ip','')}:{m.get('port',0)}\n{m.get('address','/')} {m.get('args', [])}"
                                # Use absolute screen coords for tooltip placement
                                self._show_osc_tooltip(self.root.winfo_pointerx(), self.root.winfo_pointery(), txt)
                                return
                    self._hide_osc_tooltip()
                except Exception:
                    pass

            try:
                self.canvas.bind('<Motion>', _maybe_show_osc_tooltip)
            except Exception:
                pass
        
        # Ensure only one playhead is visible
        try:
            self.canvas.delete("playhead")
        except Exception:
            pass
        playhead_x = self.playhead_pos * self.zoom_level
        self.canvas.create_line(playhead_x, 0, playhead_x, canvas_height, fill="red", width=2, tags="playhead")
        
        self.waveform_cached = True  # Mark as cached after first full draw
    
    def _draw_waveform(self, canvas_width, canvas_height, max_time):
        """Draw audio waveform on the canvas."""
        if not self.audio_data or len(self.audio_data) == 0:
            return
        
        waveform_height = min(100, canvas_height // 3)
        waveform_y_top = 30
        waveform_y_bottom = waveform_y_top + waveform_height
        waveform_center = (waveform_y_top + waveform_y_bottom) / 2
        
        # Draw background for full timeline width, not just visible area
        total_width = int(max_time * self.zoom_level) + 100
        self.canvas.create_rectangle(0, waveform_y_top, total_width, waveform_y_bottom, 
                                     fill="darkblue", outline="blue")
        
        self.canvas.create_line(0, waveform_center, total_width, waveform_center, 
                               fill="gray50", dash=(2, 2))
        
        # Draw waveform across entire timeline
        for i in range(0, total_width, 2):
            time_at_pixel = i / self.zoom_level
            if time_at_pixel > max_time:
                break
            
            sample_idx = int((time_at_pixel / self.audio_duration) * len(self.audio_data)) if self.audio_duration > 0 else 0
            sample_idx = max(0, min(sample_idx, len(self.audio_data) - 1))
            
            sample = self.audio_data[sample_idx] / 32768.0
            sample = max(-1.0, min(1.0, sample))
            
            y_offset = sample * (waveform_height / 2)
            y = waveform_center + y_offset
            
            self.canvas.create_line(i, waveform_center, i, y, fill="cyan", width=1)
    
    def _update_timeline_canvas(self):
        """Periodically update canvas (single scheduler)."""
        try:
            if self.is_playing:
                # Avoid stacking multiple draws in the same tick
                self._update_canvas_view()
        except Exception:
            pass
        # Re-arm scheduler
        self.root.after(30, self._update_timeline_canvas)
    
    def _start_dmx_monitor(self):
        """Start listening for incoming DMX."""
        self.dmx_monitor_running = True

        def monitor():
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            try:
                sock.bind((self.network_interface, 6454))
            except Exception as e:
                # If bind fails, surface the error once and stop this monitor instance
                err_msg = f"Failed to bind to {self.network_interface}: {e}"
                self.root.after(0, lambda m=err_msg: messagebox.showerror("DMX Monitor", m))
                return

            sock.settimeout(1.0)
            
            try:
                while self.dmx_monitor_running:
                    try:
                        data, _ = sock.recvfrom(1024)
                        if data.startswith(b"Art-Net\x00"):
                            universe = data[14] if len(data) > 14 else 0
                            dmx_data = data[18:18+512] if len(data) > 18 else b""
                            
                            # Update DMX display values for matching universe
                            if universe == self.selected_universe:
                                self.dmx_values[universe] = {i: dmx_data[i] if i < len(dmx_data) else 0 for i in range(512)}
                            
                            if self.recording:
                                # Check if universe should be captured (skip if filter is enabled and universe not in list)
                                should_capture = True
                                if self.universe_filter_enabled:
                                    if universe not in self.universe_filter_list:
                                        should_capture = False
                                        # Debug: Log filtered out universe
                                        if len(self.recorded_events) % 100 == 0:  # Only log occasionally to avoid spam
                                            print(f"Filtering out Universe {universe} (not in {self.universe_filter_list})")
                                
                                if should_capture:
                                    # Apply channel filter if enabled
                                    payload_data = data
                                    header = data[:18]
                                    dmx_data_full = bytearray(data[18:18+512] if len(data) > 18 else b"")
                                    if len(dmx_data_full) < 512:
                                        dmx_data_full.extend(b"\x00" * (512 - len(dmx_data_full)))
                                    any_change_vs_baseline = False

                                    if self.ignored_on_capture_enabled and universe in self.ignored_on_capture:
                                        # Record only learned channels that differ from baseline; store as sparse 'changes' dict
                                        learned = self.ignored_on_capture.get(universe, set())
                                        baseline = self.ignored_baseline.get(universe, {})
                                        changes = {}
                                        for ch in learned:
                                            if ch < 512:
                                                try:
                                                    val = int(dmx_data_full[ch])
                                                    base = int(baseline.get(ch, 0))
                                                    if val != base:
                                                        changes[ch] = val
                                                        any_change_vs_baseline = True
                                                except Exception:
                                                    pass
                                        # If no changes among learned channels, skip recording
                                        if not any_change_vs_baseline:
                                            continue
                                        sparse = True
                                    else:
                                        # Apply explicit DMX channel filter if enabled; otherwise keep full frame
                                        if self.dmx_filter_enabled and self.dmx_filter_channels:
                                            dmx_data = bytearray(512)
                                            for ch in self.dmx_filter_channels:
                                                if 0 <= ch < 512:
                                                    dmx_data[ch] = dmx_data_full[ch]
                                        else:
                                            dmx_data = dmx_data_full
                                        sparse = False

                                    payload_data = header + (bytes(dmx_data) if not (self.ignored_on_capture_enabled and universe in self.ignored_on_capture) else b"")
                                    
                                    # Use current playhead position as timestamp
                                    event = {
                                        "t": self.playhead_pos,
                                        "universe": universe,
                                        "opcode": 80,
                                        "payload": base64.b64encode(payload_data).decode("ascii") if payload_data else None,
                                        "session": getattr(self, "current_session_id", 1),
                                        # Mark sparse events so playback overlays rather than zeroing others
                                        "sparse": bool(self.ignored_on_capture_enabled and universe in self.ignored_on_capture)
                                    }
                                    if event["sparse"]:
                                        event["changes"] = changes
                                    self.recorded_events.append(event)
                                    
                                    # Sample events for live visualization (only show every 20th event to reduce overhead)
                                    if len(self.recorded_events) % 20 == 0:
                                        if not hasattr(self, 'timeline_data') or self.timeline_data is None:
                                            self.timeline_data = []
                                        self.timeline_data.append(event)
                                        # Invalidate cache to force redraw and schedule canvas update on main thread
                                        self.waveform_cached = False
                                        self.root.after(0, self._update_canvas_view)
                    except socket.timeout:
                        pass
                    except Exception:
                        pass
            finally:
                sock.close()
        
        threading.Thread(target=monitor, daemon=True).start()

    def _restart_dmx_monitor(self):
        """Restart DMX monitor with current network interface."""
        self.dmx_monitor_running = False
        # Allow previous thread to exit its recv timeout
        self.root.after(100, self._start_dmx_monitor)
    
    def _update_dmx_display(self):
        """Update DMX monitor display with live updates - optimized to only update changed values."""
        universe = self.selected_universe
        values = self.dmx_values.get(universe, {})
        
        # Get channels to update (respects filter if enabled)
        channels_to_update = self.dmx_filter_channels if self.dmx_filter_enabled else range(512)
        
        # Only update channels that have changed
        for ch in channels_to_update:
            if ch not in self.dmx_labels:
                continue
                
            val = values.get(ch, 0)
            # Skip if value hasn't changed (optimization)
            if hasattr(self, '_last_dmx_values') and self._last_dmx_values.get(ch) == val:
                continue
            
            value_label = self.dmx_labels[ch]["value"]
            
            # Update value color based on intensity
            if val == 0:
                color = "gray50"
            elif val < 85:
                color = "orange"
            elif val < 170:
                color = "yellow"
            else:
                color = "lime"
            
            value_label.config(text=f"{val:3d}", foreground=color)
            
            # Update bar
            bar = self.dmx_labels[ch]["bar"]
            bar.delete("all")
            # Use current bar canvas width for smoother scaling
            try:
                bw = max(40, int(bar.winfo_width()))
            except Exception:
                bw = 40
            bar_width = int((val / 255.0) * bw)
            if bar_width > 0:
                bar_color = color if val > 0 else "gray20"
                bar.create_rectangle(0, 0, bar_width, 8, fill=bar_color, outline=bar_color)
        
        # Cache current values for next comparison
        self._last_dmx_values = values.copy()
    
    def _update_dmx_monitor_loop(self):
        """Periodically update DMX monitor display."""
        try:
            # Skip updates during debounce window
            import time as _t
            if getattr(self, "_monitor_debounce_until", 0) and _t.time() < self._monitor_debounce_until:
                pass
            else:
                self._update_dmx_display()
        finally:
            # Lower refresh rate to reduce CPU during universe changes
            interval_ms = int(self.settings.get("dmx_monitor_refresh_ms", 200))
            interval_ms = max(100, min(1000, interval_ms))
            self.root.after(interval_ms, self._update_dmx_monitor_loop)
    
    def _toggle_monitor(self):
        """Toggle DMX monitor visibility."""
        self.monitor_visible = not self.monitor_visible
        
        if self.monitor_visible:
            # Show the monitor by adding it back to the paned window
            if self.monitor_frame not in self.paned_window.panes():
                self.paned_window.add(self.monitor_frame, stretch="always")
        else:
            # Hide the monitor by removing it from the paned window
            if self.monitor_frame in self.paned_window.panes():
                self.paned_window.forget(self.monitor_frame)
    
    @staticmethod
    def _format_time(seconds):
        """Format seconds as MM:SS.mmm"""
        td = timedelta(seconds=seconds)
        total_seconds = int(td.total_seconds())
        millis = int((seconds - total_seconds) * 1000)
        mins = total_seconds // 60
        secs = total_seconds % 60
        return f"{mins}:{secs:02d}.{millis:03d}"


def run_gui():
    """Launch the timeline editor GUI."""
    root = tk.Tk()
    app = TimelineEditorGUI(root)
    root.mainloop()


if __name__ == "__main__":
    run_gui()
