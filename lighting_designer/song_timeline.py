"""Per-song timeline editor for the Visualizer tab.

This module adds an "Edit Timeline" feature to visualizer item buttons.
Each song (visualizer item) can store a sidecar timeline of preset clips
that are triggered at specific times when the song is played.

Public API:
    open_timeline_editor(gui, item)         -> show the editor dialog
    clear_timeline(gui, item)               -> delete the sidecar
    has_timeline(gui, item) -> bool         -> whether a saved timeline exists
    start_song_timeline_playback(gui, item) -> begin firing presets in sync
    stop_song_timeline_playback(gui)        -> stop all clips and clear runtime
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import struct
import tempfile
import threading
import time
import uuid
from dataclasses import dataclass, field, asdict
from typing import Optional

from PyQt6.QtCore import (
    Qt, QRectF, QPointF, QTimer, QSize, QMimeData, QUrl, pyqtSignal, QObject,
)
from PyQt6.QtGui import (
    QPainter, QPen, QBrush, QColor, QFont, QFontMetrics, QPainterPath,
    QDrag, QAction, QKeySequence, QShortcut,
)
from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QPushButton, QLabel, QListWidget,
    QListWidgetItem, QSplitter, QFrame, QWidget, QSizePolicy, QScrollArea,
    QMessageBox, QMenu, QDoubleSpinBox, QProgressDialog, QLineEdit,
)

try:
    from .effect_engine import EffectParameters
except ImportError:
    from effect_engine import EffectParameters


# ---------------------------------------------------------------------------
#  Data model
# ---------------------------------------------------------------------------

# Fixed display length (seconds) for trigger clips on the timeline.
# Triggers are one-shot so their visual width is always this value.
_TRIGGER_DISPLAY_SEC = 1.0


@dataclass
class SongTimelineClip:
    id: str
    preset_id: str
    preset_name: str = ""
    start: float = 0.0       # seconds from song start
    length: float = 4.0      # seconds the clip plays
    color: str = "#4a90e2"
    fade_in: float = 0.0
    fade_out: float = 0.0
    # Free-form per-clip parameters (e.g. {'overlay_pct': 75.0} for the
    # built-in "Video Overlay: SET %" preset).
    params: dict = field(default_factory=dict)
    # 'preset' = normal effect preset; 'trigger' = MIDI/OSC one-shot
    clip_type: str = "preset"
    # Visual preset-lane index in the editor (0-based). Triggers ignore this.
    lane: int = 0

    @classmethod
    def make(cls, preset_id: str, preset_name: str, start: float,
             length: float = 4.0, color: str = "#4a90e2",
             clip_type: str = "preset") -> 'SongTimelineClip':
        return cls(id=str(uuid.uuid4()), preset_id=preset_id,
                   preset_name=preset_name, start=start, length=length,
                   color=color, clip_type=clip_type)

    def to_dict(self) -> dict:
        d = asdict(self)
        return d

    @classmethod
    def from_dict(cls, d: dict) -> 'SongTimelineClip':
        return cls(
            id=d.get("id", str(uuid.uuid4())),
            preset_id=d.get("preset_id", ""),
            preset_name=d.get("preset_name", ""),
            start=float(d.get("start", 0.0)),
            length=float(d.get("length", 4.0)),
            color=d.get("color", "#4a90e2"),
            fade_in=float(d.get("fade_in", 0.0)),
            fade_out=float(d.get("fade_out", 0.0)),
            params=dict(d.get("params", {}) or {}),
            clip_type=d.get("clip_type", "preset"),
            lane=max(0, int(d.get("lane", 0) or 0)),
        )


@dataclass
class SongTimeline:
    item_id: str
    duration: float = 0.0
    clips: list = field(default_factory=list)
    version: int = 2

    def to_dict(self) -> dict:
        return {
            "version": self.version,
            "item_id": self.item_id,
            "duration": self.duration,
            "clips": [c.to_dict() for c in self.clips],
        }

    @classmethod
    def from_dict(cls, d: dict) -> 'SongTimeline':
        tl = cls(
            item_id=d.get("item_id", ""),
            duration=float(d.get("duration", 0.0)),
            version=int(d.get("version", 1)),
        )
        tl.clips = [SongTimelineClip.from_dict(c) for c in d.get("clips", [])]
        return tl


# ---------------------------------------------------------------------------
#  Storage helpers
# ---------------------------------------------------------------------------

def _timeline_dir(gui) -> str:
    """Return the directory where song timelines are stored.

    Prefers a sidecar folder next to the .lighting project file.  Falls back
    to a folder in the user's home directory when no project path is set.
    """
    proj_path = getattr(gui, 'project_path', '') or ''
    if proj_path:
        base = os.path.dirname(os.path.abspath(proj_path))
    else:
        base = os.path.join(os.path.expanduser('~'), '.lighting_designer')
    d = os.path.join(base, 'song_timelines')
    os.makedirs(d, exist_ok=True)
    return d


def _timeline_path(gui, item) -> str:
    return os.path.join(_timeline_dir(gui), f"{item.id}.json")


def _waveform_cache_path(gui, item) -> str:
    return os.path.join(_timeline_dir(gui), f"{item.id}.waveform.json")


def has_timeline(gui, item) -> bool:
    try:
        return os.path.isfile(_timeline_path(gui, item))
    except Exception:
        return False


def load_timeline(gui, item) -> SongTimeline:
    p = _timeline_path(gui, item)
    if os.path.isfile(p):
        try:
            with open(p, 'r', encoding='utf-8') as f:
                return SongTimeline.from_dict(json.load(f))
        except Exception as e:
            print(f"[SongTimeline] Failed to load {p}: {e}")
    return SongTimeline(item_id=item.id)


def save_timeline(gui, item, tl: SongTimeline) -> None:
    p = _timeline_path(gui, item)
    tmp = p + '.tmp'
    try:
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(tl.to_dict(), f, indent=2)
        os.replace(tmp, p)
    except Exception as e:
        print(f"[SongTimeline] Failed to save {p}: {e}")


def clear_timeline(gui, item) -> None:
    for p in (_timeline_path(gui, item), _waveform_cache_path(gui, item)):
        try:
            if os.path.isfile(p):
                os.remove(p)
        except Exception:
            pass


# ---------------------------------------------------------------------------
#  Waveform extraction
# ---------------------------------------------------------------------------

def _find_ffmpeg() -> Optional[str]:
    p = shutil.which('ffmpeg')
    if p:
        return p
    try:
        import imageio_ffmpeg
        return imageio_ffmpeg.get_ffmpeg_exe()
    except Exception:
        return None


def _probe_duration(media_path: str) -> float:
    """Return media duration in seconds, or 0.0 on failure."""
    ff = _find_ffmpeg()
    if not ff:
        return 0.0
    # Use ffprobe-like parsing of ffmpeg -i stderr
    try:
        result = subprocess.run(
            [ff, '-i', media_path, '-f', 'null', '-'],
            capture_output=True, text=True, timeout=15,
            creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0),
        )
        out = result.stderr
        # parse "time=HH:MM:SS.xx"
        import re
        times = re.findall(r'time=(\d+):(\d+):(\d+\.?\d*)', out)
        if times:
            h, m, s = times[-1]
            return int(h) * 3600 + int(m) * 60 + float(s)
        # fall back: parse Duration line
        m = re.search(r'Duration:\s*(\d+):(\d+):(\d+\.?\d*)', out)
        if m:
            return int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
    except Exception as e:
        print(f"[SongTimeline] _probe_duration failed: {e}")
    return 0.0


def _extract_peaks(media_path: str, target_bins: int = 2000) -> tuple[list, float]:
    """Extract a (peaks, duration) tuple where peaks is a list of (min,max) per bin.

    Uses ffmpeg to decode the audio to mono s16le at 8kHz, then bins the
    samples for waveform rendering.  Returns (peaks_list, duration_seconds).
    """
    ff = _find_ffmpeg()
    if not ff:
        return [], 0.0
    duration = _probe_duration(media_path)
    sr = 8000  # downsampled — plenty for visual waveform
    try:
        proc = subprocess.Popen(
            [ff, '-v', 'quiet', '-i', media_path,
             '-vn', '-ac', '1', '-ar', str(sr), '-f', 's16le', '-'],
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0),
        )
        raw = proc.stdout.read()
        proc.wait(timeout=120)
    except Exception as e:
        print(f"[SongTimeline] _extract_peaks subprocess failed: {e}")
        return [], duration

    if not raw:
        return [], duration

    sample_count = len(raw) // 2
    if duration <= 0:
        duration = sample_count / float(sr)

    target_bins = max(100, min(target_bins, sample_count))
    samples_per_bin = max(1, sample_count // target_bins)
    peaks: list = []
    # Use struct in chunks; fast enough for typical 3-5 min songs.
    fmt = f"<{samples_per_bin}h"
    chunk_bytes = samples_per_bin * 2
    pos = 0
    for _ in range(target_bins):
        if pos + chunk_bytes > len(raw):
            break
        chunk = struct.unpack(fmt, raw[pos:pos + chunk_bytes])
        peaks.append((min(chunk) / 32768.0, max(chunk) / 32768.0))
        pos += chunk_bytes
    return peaks, duration


def _load_or_build_waveform(gui, item, on_done):
    """Build waveform peaks in a background thread, calling on_done(peaks, duration)
    on the main thread when ready.  Cached to disk per-item.
    """
    cache = _waveform_cache_path(gui, item)
    media = item.video_path or ''

    if os.path.isfile(cache):
        try:
            with open(cache, 'r', encoding='utf-8') as f:
                data = json.load(f)
            if data.get('media') == media and data.get('mtime') == _safe_mtime(media):
                peaks = [tuple(p) for p in data.get('peaks', [])]
                duration = float(data.get('duration', 0.0))
                on_done(peaks, duration)
                return
        except Exception:
            pass

    # Marshal the completion callback back to the GUI thread via a Qt signal.
    # QTimer.singleShot() called from a non-GUI worker thread silently does
    # nothing (the timer is created in a thread with no event loop), which left
    # waveforms — and any UI waiting on them — perpetually unpainted.
    class _WaveSignals(QObject):
        done = pyqtSignal(object, float)

    _sigs = _WaveSignals(gui)  # parented to gui so it lives on the GUI thread
    _sigs.done.connect(lambda peaks, duration: on_done(peaks, duration))

    def _worker():
        peaks, duration = _extract_peaks(media)
        try:
            with open(cache, 'w', encoding='utf-8') as f:
                json.dump({
                    'media': media,
                    'mtime': _safe_mtime(media),
                    'duration': duration,
                    'peaks': peaks,
                }, f)
        except Exception:
            pass
        try:
            _sigs.done.emit(peaks, duration)
        except Exception:
            pass

    threading.Thread(target=_worker, daemon=True).start()


def _safe_mtime(path: str) -> float:
    try:
        return os.path.getmtime(path)
    except Exception:
        return 0.0


# ---------------------------------------------------------------------------
#  Preset firing helpers (used by editor preview AND live playback)
# ---------------------------------------------------------------------------

def _build_effect_params(preset) -> Optional[EffectParameters]:
    try:
        params = EffectParameters.from_dict(preset.to_dict())
        if not params.target_groups and not getattr(params, 'target_fixtures', None):
            params.target_groups = list(getattr(preset, 'target_groups', []) or ['all'])
            params.target_fixtures = list(getattr(preset, 'target_fixtures', []) or [])
        return params
    except Exception as e:
        print(f"[SongTimeline] _build_effect_params failed: {e}")
        return None


_STL_DEBUG_LOG = os.path.join(os.path.expanduser('~'), 'stl_debug.txt')

def _stl_log(msg: str) -> None:
    """Write a timestamped line to the song-timeline debug log."""
    import datetime
    try:
        with open(_STL_DEBUG_LOG, 'a', encoding='utf-8') as _f:
            _f.write(f"[{datetime.datetime.now().strftime('%H:%M:%S.%f')[:-3]}] {msg}\n")
    except Exception:
        pass


# ---------------------------------------------------------------------------
#  Built-in synthetic presets (always available in the editor's preset list)
# ---------------------------------------------------------------------------
#
# These look and act like project presets to the rest of the timeline code,
# but firing them adjusts the Video Overlay Master fader directly instead of
# starting an EffectEngine HTP effect. This lets users drop "overlay on/off/
# fade" actions onto the timeline alongside their preset clips.

_BUILTIN_OVERLAY_ON      = "__overlay_on__"
_BUILTIN_OVERLAY_OFF     = "__overlay_off__"
_BUILTIN_OVERLAY_FADE_UP = "__overlay_fade_up__"
_BUILTIN_OVERLAY_FADE_DN = "__overlay_fade_down__"
_BUILTIN_OVERLAY_SET_PCT = "__overlay_set_pct__"

_BUILTIN_OVERLAY_IDS = {
    _BUILTIN_OVERLAY_ON,
    _BUILTIN_OVERLAY_OFF,
    _BUILTIN_OVERLAY_FADE_UP,
    _BUILTIN_OVERLAY_FADE_DN,
    _BUILTIN_OVERLAY_SET_PCT,
}


class _BuiltinPreset:
    """Minimal preset-like object the rest of the code can read by attr."""
    __slots__ = ("id", "name", "color", "_builtin")

    def __init__(self, pid: str, name: str, color: str):
        self.id = pid
        self.name = name
        self.color = color
        self._builtin = True

    def to_dict(self) -> dict:
        return {"id": self.id, "name": self.name, "color": self.color}


# Distinct colours/labels so they stand out in the preset list.
_BUILTIN_PRESETS: list = [
    _BuiltinPreset(_BUILTIN_OVERLAY_ON,
                   "Video Overlay: ON",      "#3fa86b"),
    _BuiltinPreset(_BUILTIN_OVERLAY_OFF,
                   "Video Overlay: OFF",     "#b04848"),
    _BuiltinPreset(_BUILTIN_OVERLAY_FADE_UP,
                   "Video Overlay: FADE UP",   "#5ec07a"),
    _BuiltinPreset(_BUILTIN_OVERLAY_FADE_DN,
                   "Video Overlay: FADE DOWN", "#c97070"),
    _BuiltinPreset(_BUILTIN_OVERLAY_SET_PCT,
                   "Video Overlay: SET %",   "#c9a04a"),
]


def _is_builtin_overlay(preset_id: str) -> bool:
    return preset_id in _BUILTIN_OVERLAY_IDS


# Track running fade timers / preview holds keyed by effect-id so we can
# cancel them when the clip ends or the user stops preview.
_overlay_active: dict = {}   # eid -> QTimer | True


def _overlay_set(gui, pct: float) -> None:
    """Set the Video Overlay Master to *pct* (0..100), going through the
    canonical handler so the UI/MIDI/detached previews stay in sync."""
    try:
        pct = max(0.0, min(100.0, float(pct)))
    except Exception:
        return
    ival = int(round(pct))
    slider = getattr(gui, 'video_overlay_slider', None)
    handler = getattr(gui, '_on_video_overlay_master_changed', None)
    settings = getattr(gui, 'app_settings', None)
    try:
        if slider is not None:
            slider.blockSignals(True)
            slider.setValue(ival)
            slider.blockSignals(False)
        if callable(handler):
            handler(ival)
        elif isinstance(settings, dict):
            settings['video_overlay_master'] = ival
            save = getattr(gui, '_save_app_settings', None)
            if callable(save):
                try:
                    save()
                except Exception:
                    pass
    except Exception as e:
        _stl_log(f"OVERLAY SET FAIL: {e}")


def _overlay_current(gui) -> float:
    settings = getattr(gui, 'app_settings', None)
    if isinstance(settings, dict):
        try:
            return float(settings.get('video_overlay_master', 0))
        except Exception:
            pass
    return 0.0


def _start_overlay_fade(gui, eid: str, start_pct: float, end_pct: float,
                        duration_s: float) -> None:
    """Run a smooth overlay fade from *start_pct* → *end_pct* over
    *duration_s* seconds, tracked under *eid* so it can be cancelled."""
    # Cancel any prior fade for this eid.
    _cancel_overlay_active(eid)
    if duration_s <= 0.05:
        _overlay_set(gui, end_pct)
        _overlay_active[eid] = True
        return
    t_start = time.monotonic()
    timer = QTimer()
    timer.setInterval(30)  # ~33 fps — plenty for an overlay fader

    def _tick():
        try:
            elapsed = time.monotonic() - t_start
            if elapsed >= duration_s:
                _overlay_set(gui, end_pct)
                try:
                    timer.stop()
                except Exception:
                    pass
                # Mark eid as still "active" (held at target) so a later
                # stop call is still a no-op but the entry can be cleared.
                _overlay_active[eid] = True
                return
            f = elapsed / duration_s
            _overlay_set(gui, start_pct + (end_pct - start_pct) * f)
        except Exception as e:
            _stl_log(f"OVERLAY FADE tick fail: {e}")
            try:
                timer.stop()
            except Exception:
                pass

    timer.timeout.connect(_tick)
    timer.start()
    _overlay_active[eid] = timer
    _stl_log(f"OVERLAY FADE: {start_pct:.0f}→{end_pct:.0f} over {duration_s:.2f}s eid={eid[:30]}")


def _cancel_overlay_active(eid: str) -> None:
    obj = _overlay_active.pop(eid, None)
    if obj is None:
        return
    try:
        if hasattr(obj, 'stop'):
            obj.stop()
    except Exception:
        pass


def _fire_overlay_builtin(gui, clip: 'SongTimelineClip', eid: str) -> None:
    """Dispatch the firing of a built-in Video Overlay clip."""
    pid = clip.preset_id
    if pid == _BUILTIN_OVERLAY_ON:
        _overlay_set(gui, 100.0)
        _overlay_active[eid] = True
    elif pid == _BUILTIN_OVERLAY_OFF:
        _overlay_set(gui, 0.0)
        _overlay_active[eid] = True
    elif pid == _BUILTIN_OVERLAY_FADE_UP:
        start_pct = _overlay_current(gui)
        _start_overlay_fade(gui, eid, start_pct, 100.0, max(0.0, clip.length))
    elif pid == _BUILTIN_OVERLAY_FADE_DN:
        start_pct = _overlay_current(gui)
        _start_overlay_fade(gui, eid, start_pct, 0.0, max(0.0, clip.length))
    elif pid == _BUILTIN_OVERLAY_SET_PCT:
        try:
            pct = float(clip.params.get('overlay_pct', 50.0))
        except Exception:
            pct = 50.0
        _overlay_set(gui, pct)
        _overlay_active[eid] = True


def _stop_overlay_builtin(gui, clip: 'SongTimelineClip', eid: str) -> None:
    """Stop / cleanup for a built-in Video Overlay clip. For snap presets
    (ON/OFF/SET %) this just clears bookkeeping — the value stays where it
    was set, so successive clips chain naturally. For fade presets we
    cancel any in-progress fade timer."""
    _cancel_overlay_active(eid)


# Tracks the list of effect ids actually started for each fired clip so
# _stop_clip can stop them all (a layered preset starts one HTP effect per
# enabled layer instead of one effect for the whole clip).
_clip_layer_eids: dict = {}  # clip eid -> list[str] of engine effect ids


def _fire_clip(gui, clip: SongTimelineClip, effect_id_prefix: str = "stl") -> None:
    # Trigger clip: fire-and-forget MIDI/OSC send.
    if getattr(clip, 'clip_type', 'preset') == 'trigger':
        _fire_trigger(gui, clip)
        return
    # Timeline fixture sequence clip: play it via the sequence player.
    if _is_sequence_preset(clip.preset_id):
        _fire_sequence(gui, clip)
        return
    eid = f"{effect_id_prefix}_{clip.id}"
    # Built-in Video Overlay presets bypass the effect engine entirely.
    if _is_builtin_overlay(clip.preset_id):
        _stl_log(f"FIRE BUILTIN: eid={eid[:30]} kind={clip.preset_id} dur={clip.length:.2f}")
        try:
            _fire_overlay_builtin(gui, clip, eid)
        except Exception as e:
            _stl_log(f"FIRE BUILTIN EXC: {e}")
        return
    eng = getattr(gui, 'effect_engine', None)
    if not eng:
        _stl_log(f"FIRE SKIP (no engine): clip={clip.id[:8]} preset={clip.preset_id[:8]}")
        return
    preset = _find_preset(gui, clip.preset_id)
    if not preset:
        _stl_log(f"FIRE SKIP (preset not found): clip={clip.id[:8]} preset_id={clip.preset_id}")
        return

    # ── Layered preset path (mirrors gui._execute_preset for button clicks) ──
    # A preset with a non-empty `layers` list must be fired layer-by-layer
    # through the HTP engine so layer_type → effect_type mapping (dimmer,
    # strobe, pulse, etc.) happens in EffectLayer.to_effect_params().
    layers_data = list(getattr(preset, 'layers', None) or [])
    if layers_data:
        # Lazy import to avoid circular dependency with gui.py / models.py.
        try:
            from .models import EffectLayer
        except ImportError:
            from models import EffectLayer
        started: list = []
        _stl_log(f"FIRE LAYERED: eid={eid[:30]} layers={len(layers_data)} duration={clip.length:.2f}s")
        for idx, ld in enumerate(layers_data):
            try:
                layer = EffectLayer.from_dict(ld)
                if not layer.enabled:
                    continue
                params = layer.to_effect_params()
                # Mirror the safeguard in gui._execute_preset: prevent a
                # default intensity layer (0..100) from being treated as a
                # pulse when the user just wanted a hold.
                if (layer.layer_type == 'intensity'
                        and layer.effect_type == 'static'
                        and params.effect_type == 'pulse'):
                    params.effect_type = 'static'
                    params.intensity_min = layer.intensity
                    params.intensity_max = layer.intensity
                layer_eid = f"{eid}__L{idx}_{layer.id}"
                try:
                    eng.start_effect_htp(layer_eid, params,
                                         fade_in_time=clip.fade_in,
                                         fade_out_time=clip.fade_out,
                                         effect_duration=clip.length)
                except TypeError:
                    eng.start_effect_htp(layer_eid, params)
                started.append(layer_eid)
            except Exception as e:
                _stl_log(f"FIRE LAYER EXC idx={idx}: {e}")
        if started:
            _clip_layer_eids[eid] = started
        return

    # ── Single-effect (non-layered) preset path ──
    params = _build_effect_params(preset)
    if not params:
        _stl_log(f"FIRE SKIP (no params): clip={clip.id[:8]}")
        return
    _stl_log(f"FIRE: eid={eid[:30]} duration={clip.length:.2f}s start={clip.start:.2f}")
    try:
        eng.start_effect_htp(eid, params,
                             fade_in_time=clip.fade_in,
                             fade_out_time=clip.fade_out,
                             effect_duration=clip.length)
    except TypeError:
        # Older signature — fall back without keyword args we know exist.
        eng.start_effect_htp(eid, params)


def _stop_clip(gui, clip: SongTimelineClip, effect_id_prefix: str = "stl") -> None:
    # Trigger clips are fire-and-forget — nothing to stop.
    if getattr(clip, 'clip_type', 'preset') == 'trigger':
        return
    # Timeline fixture sequence clip: stop the sequence player.
    if _is_sequence_preset(clip.preset_id):
        _stop_sequence(gui, clip)
        return
    eid = f"{effect_id_prefix}_{clip.id}"
    if _is_builtin_overlay(clip.preset_id):
        try:
            _stop_overlay_builtin(gui, clip, eid)
        except Exception as e:
            _stl_log(f"STOP BUILTIN EXC: {e}")
        return
    eng = getattr(gui, 'effect_engine', None)
    if not eng:
        _stl_log(f"STOP SKIP (no engine): clip={clip.id[:8]}")
        return
    # Layered clip: stop each per-layer effect id we recorded at fire time.
    layer_eids = _clip_layer_eids.pop(eid, None)
    if layer_eids:
        _stl_log(f"STOP LAYERED: eid={eid[:30]} layer_count={len(layer_eids)}")
        for leid in layer_eids:
            try:
                eng.stop_effect_htp(leid)
            except Exception as e:
                _stl_log(f"STOP LAYER EXC {leid[:30]}: {e}")
        return
    active = getattr(eng, '_active_effects', {})
    found = eid in active
    _stl_log(f"STOP: eid={eid[:30]} found_in_active={found} active_count={len(active)}")
    try:
        eng.stop_effect_htp(eid)
    except Exception as e:
        _stl_log(f"STOP EXCEPTION: {e}")


def _is_sequence_preset(preset_id) -> bool:
    return isinstance(preset_id, str) and preset_id.startswith("sequence:")


def _fire_sequence(gui, clip: SongTimelineClip) -> None:
    """Start a timeline fixture sequence for the duration of the clip."""
    seq_id = clip.preset_id.split(":", 1)[1]
    if seq_id in getattr(gui, '_active_sequence_players', {}):
        return
    try:
        gui._toggle_fixture_sequence(seq_id)
    except Exception as e:
        _stl_log(f"FIRE SEQ EXC: {e}")


def _stop_sequence(gui, clip: SongTimelineClip) -> None:
    seq_id = clip.preset_id.split(":", 1)[1]
    try:
        gui._stop_fixture_sequence(seq_id, restore=True)
    except Exception as e:
        _stl_log(f"STOP SEQ EXC: {e}")


def _find_preset(gui, preset_id: str):
    # Built-in synthetic presets first — they're not in the project.
    if _is_builtin_overlay(preset_id):
        for bp in _BUILTIN_PRESETS:
            if bp.id == preset_id:
                return bp
    proj = getattr(gui, 'project', None)
    if not proj:
        return None
    # Try the documented helper first
    fn = getattr(proj, 'get_preset_by_id', None)
    if callable(fn):
        try:
            res = fn(preset_id)
            if res:
                return res
        except Exception:
            pass
    for p in getattr(proj, 'presets', []) or []:
        if getattr(p, 'id', None) == preset_id:
            return p
    return None


def _all_presets(gui) -> list:
    proj = getattr(gui, 'project', None)
    project_presets = list(getattr(proj, 'presets', []) or []) if proj else []
    # Built-in synthetic presets always appear first.
    return list(_BUILTIN_PRESETS) + project_presets


def _all_shortcuts(gui) -> list:
    """Return all Shortcut objects from all shortcut pages."""
    proj = getattr(gui, 'project', None)
    if not proj:
        return []
    result = []
    for page in getattr(proj, 'shortcut_pages', []) or []:
        result.extend(getattr(page, 'shortcuts', []) or [])
    return result


def _find_shortcut(gui, shortcut_id: str):
    """Find a Shortcut by id."""
    for sc in _all_shortcuts(gui):
        if getattr(sc, 'id', None) == shortcut_id:
            return sc
    return None


def _fire_trigger(gui, clip: SongTimelineClip) -> None:
    """Fire a MIDI/OSC shortcut trigger clip."""
    sc = _find_shortcut(gui, clip.preset_id)
    if sc is None:
        _stl_log(f"TRIGGER SKIP: shortcut not found id={clip.preset_id}")
        return
    _stl_log(f"TRIGGER FIRE: {sc.name}")
    if getattr(sc, 'osc_enabled', False):
        try:
            gui._send_osc_message(sc.osc_ip, sc.osc_port, sc.osc_address,
                                  list(sc.osc_args or []))
        except Exception as e:
            _stl_log(f"TRIGGER OSC error: {e}")
    if getattr(sc, 'midi_enabled', False):
        try:
            gui._send_midi_message(sc.midi_type, sc.midi_channel,
                                   sc.midi_note, sc.midi_velocity,
                                   sc.midi_duration)
        except Exception as e:
            _stl_log(f"TRIGGER MIDI error: {e}")


# ---------------------------------------------------------------------------
#  Live playback controller (fires clips while the song plays)
# ---------------------------------------------------------------------------

class _RuntimePlayer:
    """Drives clip firing for a single song during normal playback (no editor)."""
    MIME = "application/x-ld-song-timeline-runtime"

    def __init__(self, gui, item, tl: SongTimeline):
        self.gui = gui
        self.item = item
        self.tl = tl
        self._active_clips: dict = {}   # clip_id -> clip
        self._fired_triggers: set = set()  # clip_ids already fired
        self._timer = QTimer()
        self._timer.setInterval(30)
        self._timer.timeout.connect(self._tick)
        # Snapshot the engine's _start_time when we start so we can keep
        # ticking through crossfades (when _viz_active_item_id switches to
        # the next song while this song's audio is still fading out).
        self._engine_start_time: float | None = None
        # Effective end of this song (trim_end or 0 = natural end, resolved later).
        self._effective_end: float = 0.0

    def start(self) -> None:
        engine = getattr(self.gui, '_viz_engine', None)
        if engine is not None:
            self._engine_start_time = getattr(engine, '_start_time', None)
        # Compute effective end (trim_end if set, else 0 = run until all clips done)
        self._effective_end = float(getattr(self.item, 'trim_end', 0.0) or 0.0)
        self._timer.start()

    def stop(self) -> None:
        self._timer.stop()
        for clip in list(self._active_clips.values()):
            _stop_clip(self.gui, clip)
        self._active_clips.clear()
        self._fired_triggers.clear()

    def _elapsed(self) -> float:
        # Use the snapshotted start time so we keep ticking correctly even
        # after the engine has moved on to the next song in a crossfade.
        st = self._engine_start_time
        if not st:
            # Fallback: read from the engine directly (first tick before start() called)
            engine = getattr(self.gui, '_viz_engine', None)
            if engine is None:
                return 0.0
            st = getattr(engine, '_start_time', None)
            if not st:
                return 0.0
        return time.time() - st

    def _effective_duration(self) -> float:
        """Return the last meaningful timeline position for this song."""
        if not self.tl.clips:
            return 0.0
        return max((c.start + (c.length if getattr(c, 'clip_type', 'preset') == 'preset' else 0.0))
                   for c in self.tl.clips)

    def _tick(self) -> None:
        try:
            active_id = getattr(self.gui, '_viz_active_item_id', None)
            # While we are the live song, keep our start-time anchor in sync
            # with the engine's. The engine applies trim_start ("start later")
            # via a delayed seek that re-anchors _start_time ~80ms after play;
            # snapshotting only once at start() would leave a stale anchor and
            # fire every clip trim_start seconds too late.
            if active_id == self.item.id:
                engine = getattr(self.gui, '_viz_engine', None)
                if engine is not None:
                    live_st = getattr(engine, '_start_time', None)
                    if live_st:
                        self._engine_start_time = live_st

            t = self._elapsed()

            # Allow ticking through crossfades: only stop once the active
            # item has genuinely changed AND we've passed all clip windows.
            if active_id != self.item.id:
                # The engine has moved on (crossfade or manual stop). Keep
                # firing triggers/clips through the overlap window so the
                # end-of-song MIDI/OSC triggers still fire. The +1.0s grace
                # ensures a trigger sitting exactly at `end` gets dispatched
                # by the firing loop below before we stop.
                end = self._effective_end if self._effective_end > 0 else self._effective_duration()
                if end <= 0 or t > end + 1.0:
                    self.stop()
                    return
                # Otherwise fall through — keep firing remaining triggers.

            to_fire: list = []
            to_stop: list = []
            for clip in self.tl.clips:
                cid = clip.id
                is_trigger = getattr(clip, 'clip_type', 'preset') == 'trigger'
                if is_trigger:
                    # Fire once when playhead crosses start; never track as active.
                    if t >= clip.start and cid not in self._fired_triggers:
                        self._fired_triggers.add(cid)
                        to_fire.append(clip)
                    continue
                in_window = clip.start <= t < (clip.start + clip.length)
                if in_window and cid not in self._active_clips:
                    self._active_clips[cid] = clip
                    to_fire.append(clip)
                elif not in_window and cid in self._active_clips:
                    self._active_clips.pop(cid, None)
                    to_stop.append(clip)
            if to_fire or to_stop:
                gui = self.gui
                def _dispatch(fire=to_fire, stop=to_stop, g=gui):
                    for c in stop:
                        try:
                            _stop_clip(g, c)
                        except Exception as e:
                            print(f"[SongTimeline] runtime _stop_clip failed: {e}")
                    for c in fire:
                        try:
                            _fire_clip(g, c)
                        except Exception as e:
                            print(f"[SongTimeline] runtime _fire_clip failed: {e}")
                QTimer.singleShot(0, _dispatch)
        except Exception as e:
            print(f"[SongTimeline] runtime _tick exception: {e}")
            import traceback; traceback.print_exc()


_active_runtime: Optional[_RuntimePlayer] = None
# Runtimes that are finishing their end-of-song triggers during a cue
# crossfade. They self-terminate in _RuntimePlayer._tick once their playhead
# passes the last clip/trigger, and are pruned on the next start/stop.
_fading_runtimes: list = []
# Saved Video Overlay Master value while a song-timeline is driving the rig.
# None when no suppression is currently in effect.
_saved_video_overlay_master: Optional[int] = None


def _suppress_video_overlay_master(gui) -> None:
    """Force the Video Overlay Master to 0 so a generic video doesn't bleed
    onto the lights while a programmed timeline is driving them.

    The previous value is stashed so :func:`_restore_video_overlay_master`
    can put it back when playback stops.
    """
    global _saved_video_overlay_master
    if _saved_video_overlay_master is not None:
        return  # already suppressed
    settings = getattr(gui, 'app_settings', None)
    if not isinstance(settings, dict):
        return
    try:
        prev = int(settings.get('video_overlay_master', 100))
    except Exception:
        prev = 100
    if prev <= 0:
        # Nothing to do — overlay already off. Don't clobber on restore.
        return
    _saved_video_overlay_master = prev
    # Update via the slider when it exists so the UI label, MIDI feedback,
    # detached previews, and settings file all stay in sync. Fall back to a
    # direct setting write if the slider isn't built yet.
    slider = getattr(gui, 'video_overlay_slider', None)
    handler = getattr(gui, '_on_video_overlay_master_changed', None)
    try:
        if slider is not None:
            slider.blockSignals(True)
            slider.setValue(0)
            slider.blockSignals(False)
        if callable(handler):
            handler(0)
        else:
            settings['video_overlay_master'] = 0
            save = getattr(gui, '_save_app_settings', None)
            if callable(save):
                try:
                    save()
                except Exception:
                    pass
    except Exception as e:
        _stl_log(f"OVERLAY SUPPRESS FAIL: {e}")
        return
    _stl_log(f"OVERLAY SUPPRESS: prev={prev} → 0 (timeline-driven song)")


def _restore_video_overlay_master(gui) -> None:
    """Restore the Video Overlay Master to whatever it was before
    :func:`_suppress_video_overlay_master` ran. No-op if nothing was saved."""
    global _saved_video_overlay_master
    prev = _saved_video_overlay_master
    if prev is None:
        return
    _saved_video_overlay_master = None
    slider = getattr(gui, 'video_overlay_slider', None)
    handler = getattr(gui, '_on_video_overlay_master_changed', None)
    settings = getattr(gui, 'app_settings', None)
    try:
        if slider is not None:
            slider.blockSignals(True)
            slider.setValue(int(prev))
            slider.blockSignals(False)
        if callable(handler):
            handler(int(prev))
        elif isinstance(settings, dict):
            settings['video_overlay_master'] = int(prev)
            save = getattr(gui, '_save_app_settings', None)
            if callable(save):
                try:
                    save()
                except Exception:
                    pass
    except Exception as e:
        _stl_log(f"OVERLAY RESTORE FAIL: {e}")
        return
    _stl_log(f"OVERLAY RESTORE: → {prev}")


def detach_active_runtime_for_crossfade(gui) -> None:
    """Move the active runtime into the 'fading' set so it keeps firing its
    end-of-song MIDI/OSC triggers through a cue crossfade instead of being
    killed when the next song's timeline starts.

    Called by the Cue player right before it crossfades to the next song.
    The detached runtime self-terminates inside :meth:`_RuntimePlayer._tick`
    once its playhead passes the last clip/trigger.
    """
    global _active_runtime, _fading_runtimes
    _prune_fading_runtimes()
    if _active_runtime is not None:
        _fading_runtimes.append(_active_runtime)
        _active_runtime = None


def _prune_fading_runtimes() -> None:
    """Drop any fading runtimes whose timer has already stopped."""
    global _fading_runtimes
    _fading_runtimes = [r for r in _fading_runtimes
                        if getattr(r, '_timer', None) is not None and r._timer.isActive()]


def _stop_active_runtime_only(gui) -> None:
    """Stop only the current active runtime (a direct song switch). Fading
    runtimes detached for a crossfade keep running so their end triggers
    fire. Overlay master is only restored when nothing is still driving."""
    global _active_runtime
    if _active_runtime is not None:
        try:
            _active_runtime.stop()
        except Exception:
            pass
        _active_runtime = None
    _prune_fading_runtimes()
    if not _fading_runtimes:
        try:
            _restore_video_overlay_master(gui)
        except Exception as e:
            _stl_log(f"OVERLAY RESTORE outer fail: {e}")


def start_song_timeline_playback(gui, item) -> None:
    """Begin firing preset clips for *item* in sync with engine playback."""
    global _active_runtime
    # Stop only the active runtime — a crossfading (detached) runtime keeps
    # going so its end-of-song triggers still fire during the overlap.
    _stop_active_runtime_only(gui)
    if not has_timeline(gui, item):
        return
    tl = load_timeline(gui, item)
    if not tl.clips:
        return
    # A song with a programmed timeline owns the rig — silence the generic
    # video-overlay pass so plain video pixels don't bleed onto the lights
    # on top of the programmed presets. Restored on stop.
    try:
        _suppress_video_overlay_master(gui)
    except Exception as e:
        _stl_log(f"OVERLAY SUPPRESS outer fail: {e}")
    # Hard stop any other HTP effects so this song drives the rig.
    eng = getattr(gui, 'effect_engine', None)
    if eng is not None:
        try:
            if getattr(eng, '_active_effects', None):
                eng.stop_all_effects_htp(blackout=False, go_home=False)
        except Exception:
            pass
    rt = _RuntimePlayer(gui, item, tl)
    _active_runtime = rt
    rt.start()

def stop_song_timeline_playback(gui) -> None:
    """Full stop — kills the active runtime AND any fading (crossfading)
    runtimes. Used for genuine stops (Stop button, _stop_visualizer)."""
    global _active_runtime, _fading_runtimes
    if _active_runtime is not None:
        try:
            _active_runtime.stop()
        except Exception:
            pass
        _active_runtime = None
    for r in _fading_runtimes:
        try:
            r.stop()
        except Exception:
            pass
    _fading_runtimes = []
    # Always try to restore — safe no-op if nothing was suppressed.
    try:
        _restore_video_overlay_master(gui)
    except Exception as e:
        _stl_log(f"OVERLAY RESTORE outer fail: {e}")


def _stop_external_playback_for_timeline(gui) -> None:
    """Stop any playback/effects outside the timeline editor.

    Opening or using the song timeline should give the timeline full ownership
    of playback so users don't hear/see stale songs or effects from elsewhere.
    """
    # Stop any active runtime from this module first.
    try:
        stop_song_timeline_playback(gui)
    except Exception:
        pass

    # Stop cue playback if active.
    try:
        cp = getattr(gui, '_cue_player', None)
        if cp and (getattr(cp, 'is_playing', False) or getattr(cp, 'is_paused', False)):
            cp.stop()
    except Exception:
        pass

    # Stop visualizer/song playback in the main UI.
    try:
        try:
            from .visualizer_tab import _stop_visualizer
        except ImportError:
            from visualizer_tab import _stop_visualizer
        _stop_visualizer(gui)
    except Exception:
        # Fallback: direct engine stop if helper import fails.
        try:
            eng = getattr(gui, '_viz_engine', None)
            if eng is not None and getattr(eng, 'is_playing', False):
                eng.stop()
        except Exception:
            pass

    # Stop execute/quick effects so timeline edits start from a clean state.
    try:
        eff = getattr(gui, 'effect_engine', None)
        if eff is not None:
            try:
                eff.stop_all_effects_htp(blackout=False, go_home=False)
            except Exception:
                pass
            try:
                eff._execute_mode = False
            except Exception:
                pass
            try:
                eff.stop_effect(blackout=False, send_home=False)
            except Exception:
                pass
    except Exception:
        pass


# ---------------------------------------------------------------------------
#  Editor widgets
# ---------------------------------------------------------------------------

# MIME type used when dragging a preset entry onto the timeline canvas.
_PRESET_MIME = "application/x-ld-preset-id"


class _PresetListWidget(QListWidget):
    """Left-side list of available presets, draggable onto the timeline."""

    # Emitted when the user requests preview/stop from the right-click menu
    # or via item activation. Editor wires these to its preview engine.
    previewRequested = pyqtSignal(str, str)   # (preset_id, preset_name)
    stopPreviewRequested = pyqtSignal()
    # Emitted whenever the user begins interacting with a different preset
    # (selection change or drag start) so the editor can cancel any active
    # preview per the UX spec ("clicking any other preset stops preview").
    interactionStarted = pyqtSignal()

    def __init__(self, gui, parent=None):
        super().__init__(parent)
        self.gui = gui
        self.setDragEnabled(True)
        self.setSelectionMode(QListWidget.SelectionMode.SingleSelection)
        self.setStyleSheet("""
            QListWidget { background: #1f1f1f; color: #ddd; border: 1px solid #333; }
            QListWidget::item { padding: 6px; border-bottom: 1px solid #2a2a2a; }
            QListWidget::item:selected { background: #2d5a8e; color: #fff; }
        """)
        # Right-click menu for preview/stop-preview
        self.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.customContextMenuRequested.connect(self._on_context_menu)
        # Clicking on a different preset should cancel any running preview.
        self.itemClicked.connect(lambda _it: self.interactionStarted.emit())
        # Double-click triggers preview as a convenience.
        self.itemDoubleClicked.connect(self._on_double_click)
        self.refresh()

    def _on_context_menu(self, pos):
        item = self.itemAt(pos)
        menu = QMenu(self)
        if item is not None:
            pid = item.data(Qt.ItemDataRole.UserRole) or ''
            name = item.data(Qt.ItemDataRole.UserRole + 1) or ''
            act_preview = menu.addAction("▶  Preview Effect")
            act_stop = menu.addAction("■  Stop Preview")
            chosen = menu.exec(self.mapToGlobal(pos))
            if chosen is act_preview and pid:
                self.previewRequested.emit(pid, name)
            elif chosen is act_stop:
                self.stopPreviewRequested.emit()
        else:
            act_stop = menu.addAction("■  Stop Preview")
            chosen = menu.exec(self.mapToGlobal(pos))
            if chosen is act_stop:
                self.stopPreviewRequested.emit()

    def _on_double_click(self, item):
        if item is None:
            return
        pid = item.data(Qt.ItemDataRole.UserRole) or ''
        name = item.data(Qt.ItemDataRole.UserRole + 1) or ''
        if pid:
            self.previewRequested.emit(pid, name)

    def refresh(self, search: str = "") -> None:
        self.clear()
        s = (search or "").strip().lower()
        for p in _all_presets(self.gui):
            name = getattr(p, 'name', '?')
            if s and s not in name.lower():
                continue
            is_builtin = bool(getattr(p, '_builtin', False))
            icon = "📺" if is_builtin else "🎬"
            it = QListWidgetItem(f"{icon}  {name}")
            it.setData(Qt.ItemDataRole.UserRole, getattr(p, 'id', ''))
            it.setData(Qt.ItemDataRole.UserRole + 1, name)
            color = getattr(p, 'color', '') or '#4a90e2'
            it.setData(Qt.ItemDataRole.UserRole + 2, color)
            it.setData(Qt.ItemDataRole.UserRole + 3, False)  # is_trigger
            if is_builtin:
                # Tag built-ins visually so users can tell them apart from
                # their own presets at a glance.
                try:
                    it.setForeground(QColor(color))
                    f = it.font(); f.setBold(True); it.setFont(f)
                    it.setToolTip(
                        "Built-in Video Overlay control. Drop onto the "
                        "timeline to drive the Video Overlay Master fader."
                    )
                except Exception:
                    pass
            self.addItem(it)

        # ── Timeline fixture sequences (played via the sequence player) ──
        proj = getattr(self.gui, 'project', None)
        for seq in (getattr(proj, 'fixture_sequences', []) or []):
            name = getattr(seq, 'name', 'Sequence')
            if s and s not in name.lower():
                continue
            it = QListWidgetItem(f"\U0001f39e\ufe0f  {name}")
            it.setData(Qt.ItemDataRole.UserRole, f"sequence:{getattr(seq, 'id', '')}")
            it.setData(Qt.ItemDataRole.UserRole + 1, name)
            it.setData(Qt.ItemDataRole.UserRole + 2, '#4a9a8a')
            it.setData(Qt.ItemDataRole.UserRole + 3, False)  # is_trigger
            it.setToolTip(
                "Timeline fixture sequence. Drop onto the timeline to play it "
                "during the song."
            )
            try:
                it.setForeground(QColor('#4a9a8a'))
            except Exception:
                pass
            self.addItem(it)

        # ── MIDI / OSC Trigger section ──────────────────────────────────
        shortcuts = _all_shortcuts(self.gui)
        if shortcuts:
            # Separator header (not interactive)
            sep = QListWidgetItem("\u2500\u2500 MIDI / OSC Triggers \u2500\u2500")
            sep.setFlags(Qt.ItemFlag.NoItemFlags)
            sep.setForeground(QColor("#888888"))
            f = sep.font(); f.setItalic(True); sep.setFont(f)
            self.addItem(sep)
            for sc in shortcuts:
                name = getattr(sc, 'name', '?')
                if s and s not in name.lower():
                    continue
                osc_on = getattr(sc, 'osc_enabled', False)
                midi_on = getattr(sc, 'midi_enabled', False)
                if osc_on and midi_on:
                    icon = "📡🎹"
                elif midi_on:
                    icon = "🎹"
                else:
                    icon = "📡"
                color = getattr(sc, 'color', '#c97a50') or '#c97a50'
                it = QListWidgetItem(f"{icon}  {name}")
                it.setData(Qt.ItemDataRole.UserRole, getattr(sc, 'id', ''))
                it.setData(Qt.ItemDataRole.UserRole + 1, name)
                it.setData(Qt.ItemDataRole.UserRole + 2, color)
                it.setData(Qt.ItemDataRole.UserRole + 3, True)  # is_trigger
                # Build a short tooltip describing what will be sent
                tip_parts = []
                if osc_on:
                    tip_parts.append(f"OSC: {sc.osc_address}")
                if midi_on:
                    tip_parts.append(f"MIDI: {sc.midi_type} ch{sc.midi_channel} note{sc.midi_note}")
                it.setToolTip("\n".join(tip_parts) if tip_parts else name)
                try:
                    it.setForeground(QColor(color))
                except Exception:
                    pass
                self.addItem(it)

    def startDrag(self, supportedActions):
        item = self.currentItem()
        if not item:
            return
        # Skip separator items (no UserRole id)
        if not item.flags() & Qt.ItemFlag.ItemIsEnabled:
            return
        # Per spec: dragging a preset onto the timeline must stop any
        # currently-active live preview.
        self.interactionStarted.emit()
        pid = item.data(Qt.ItemDataRole.UserRole)
        if not pid:
            return
        name = item.data(Qt.ItemDataRole.UserRole + 1) or ''
        color = item.data(Qt.ItemDataRole.UserRole + 2) or '#4a90e2'
        is_trigger = bool(item.data(Qt.ItemDataRole.UserRole + 3))
        mime = QMimeData()
        payload = json.dumps({"id": pid, "name": name, "color": color,
                              "is_trigger": is_trigger})
        mime.setData(_PRESET_MIME, payload.encode('utf-8'))
        mime.setText(name)
        drag = QDrag(self)
        drag.setMimeData(mime)
        drag.exec(Qt.DropAction.CopyAction)


class _TimelineCanvas(QFrame):
    """The scrolling timeline canvas with waveform + clip lane(s).

    Layout (vertical):
        time ruler      (28 px)
        waveform        (90 px)
        preset lane     (rest - TRIGGER_LANE_H)
        trigger lane    (TRIGGER_LANE_H px)  — MIDI/OSC one-shots
    """

    RULER_H = 28
    WAVE_H = 90
    TRIGGER_LANE_H = 60   # fixed height for MIDI/OSC trigger row
    PRESET_LANE_H = 44
    PRESET_LANE_GAP = 2
    PRESET_MAX_LANES = 5
    PRESET_DRAW_PAD_Y = 4

    selectionChanged = pyqtSignal(object)   # emits clip or None
    changed = pyqtSignal()                  # emits when clips mutate
    trimChanged = pyqtSignal(float, float)  # emits (trim_start, trim_end) on drag release

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptDrops(True)
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setMinimumHeight(320)  # extra TRIGGER_LANE_H vs old 260
        self.setStyleSheet("background: #141414;")

        self.duration: float = 60.0
        self.peaks: list = []
        self.clips: list = []           # list[SongTimelineClip]
        self.pixels_per_sec: float = 50.0
        self.playhead: float = 0.0
        self._selected_id: Optional[str] = None
        # Additional selection set for multi-select (Ctrl/Shift+click). Always
        # contains _selected_id when not None. Stored as a set of clip ids.
        self._selected_ids: set = set()
        self._drag_mode: Optional[str] = None    # 'move' | 'resize_l' | 'resize_r' | 'seek'
        self._drag_clip: Optional[SongTimelineClip] = None
        self._drag_grab_dx: float = 0.0
        self._drag_original = None     # (start, length) for undo cancel
        # When dragging multiple clips at once, remember each clip's offset
        # from the dragged clip so they all move together.
        self._drag_group_offsets: dict = {}
        self._clipboard: Optional[dict] = None     # legacy single-clip slot
        self._clipboard_multi: list = []           # list[dict] for multi-clip copy

        # Per-song trim (seconds).  trim_end = 0.0 means "natural end".
        self.trim_start: float = 0.0
        self.trim_end: float = 0.0
        self._trim_drag: Optional[str] = None      # 'trim_start' | 'trim_end'

        # Preset lane state and drag preview.
        self._lane_states: dict[int, dict] = {0: {'mute': False, 'solo': False, 'lock': False}}
        self._dnd_preview: Optional[dict] = None
        self._move_preview_lane: Optional[int] = None
        self._move_preview_reason: str = ""
        self._preset_target_map: dict[str, dict] = {}
        self._conflict_pairs: dict[frozenset, str] = {}

        self._refresh_minimum_height()

    # ---- coordinate helpers ----
    def time_to_x(self, t: float) -> float:
        return t * self.pixels_per_sec

    def x_to_time(self, x: float) -> float:
        return max(0.0, x / self.pixels_per_sec)

    def total_width(self) -> int:
        return max(800, int(self.duration * self.pixels_per_sec) + 40)

    def sizeHint(self) -> QSize:
        return QSize(self.total_width(), self._calc_canvas_height())

    def minimumSizeHint(self) -> QSize:
        return QSize(self.total_width(), self._calc_canvas_height())

    def set_zoom(self, pixels_per_sec: float) -> None:
        self.pixels_per_sec = max(5.0, min(400.0, pixels_per_sec))
        self.updateGeometry()
        self.update()

    def set_data(self, duration: float, peaks: list, clips: list) -> None:
        self.duration = max(duration, 1.0)
        self.peaks = peaks or []
        self.clips = clips
        self._normalize_preset_lanes()
        self._refresh_conflict_cache()
        self._refresh_minimum_height()
        self.updateGeometry()
        self.update()

    def set_preset_target_map(self, target_map: dict) -> None:
        self._preset_target_map = dict(target_map or {})
        self._refresh_conflict_cache()
        self.update()

    def lane_count(self) -> int:
        lanes = [getattr(c, 'lane', 0) for c in self.clips if getattr(c, 'clip_type', 'preset') == 'preset']
        count = (max(lanes) + 1) if lanes else 1
        return max(1, min(self.PRESET_MAX_LANES, count))

    def set_lane_state(self, lane: int, key: str, value: bool) -> None:
        if key not in ('mute', 'solo', 'lock'):
            return
        lane = max(0, min(self.PRESET_MAX_LANES - 1, int(lane)))
        st = self._lane_states.setdefault(lane, {'mute': False, 'solo': False, 'lock': False})
        st[key] = bool(value)
        self.update()

    def get_lane_state(self, lane: int) -> dict:
        lane = max(0, min(self.PRESET_MAX_LANES - 1, int(lane)))
        return dict(self._lane_states.get(lane, {'mute': False, 'solo': False, 'lock': False}))

    def _is_lane_locked(self, lane: int) -> bool:
        return bool(self._lane_states.get(int(lane), {}).get('lock', False))

    def _is_lane_muted(self, lane: int) -> bool:
        return bool(self._lane_states.get(int(lane), {}).get('mute', False))

    def _has_any_solo(self) -> bool:
        for i in range(self.PRESET_MAX_LANES):
            if self._lane_states.get(i, {}).get('solo', False):
                return True
        return False

    def is_clip_audible(self, clip: SongTimelineClip) -> bool:
        if getattr(clip, 'clip_type', 'preset') != 'preset':
            return True
        lane = max(0, int(getattr(clip, 'lane', 0) or 0))
        if self._has_any_solo():
            return bool(self._lane_states.get(lane, {}).get('solo', False))
        return not self._is_lane_muted(lane)

    def _calc_canvas_height(self) -> int:
        lanes = self.lane_count()
        preset_h = lanes * self.PRESET_LANE_H + max(0, lanes - 1) * self.PRESET_LANE_GAP
        return self.RULER_H + self.WAVE_H + self.TRIGGER_LANE_H + preset_h + 8

    def _refresh_minimum_height(self) -> None:
        h = self._calc_canvas_height()
        self.setMinimumHeight(h)

    def _preset_layout(self, h: Optional[int] = None) -> tuple[int, int, int, int]:
        total_h = self.height() if h is None else int(h)
        lane_top = self.RULER_H + self.WAVE_H
        lanes = self.lane_count()
        preset_lane_h = lanes * self.PRESET_LANE_H + max(0, lanes - 1) * self.PRESET_LANE_GAP
        trigger_lane_top = lane_top + preset_lane_h
        return lane_top, trigger_lane_top, preset_lane_h, lanes

    def _lane_rect(self, lane: int, lane_top: int) -> QRectF:
        lane = max(0, min(self.PRESET_MAX_LANES - 1, int(lane)))
        y = lane_top + lane * (self.PRESET_LANE_H + self.PRESET_LANE_GAP)
        return QRectF(0, y, self.width(), self.PRESET_LANE_H)

    def _lane_for_y(self, y: float, lane_top: int, lanes: int) -> int:
        if lanes <= 1:
            return 0
        rel = max(0.0, y - lane_top)
        step = self.PRESET_LANE_H + self.PRESET_LANE_GAP
        lane = int(rel // step) if step > 0 else 0
        return max(0, min(lanes - 1, lane))

    def _preset_overlap(self, a_start: float, a_len: float, b_start: float, b_len: float) -> bool:
        a_end = a_start + max(0.0, a_len)
        b_end = b_start + max(0.0, b_len)
        return (a_start < b_end - 1e-6) and (a_end > b_start + 1e-6)

    def _preset_overlaps_in_lane(self, start: float, length: float, lane: int, ignore_ids: Optional[set] = None) -> bool:
        ignore_ids = ignore_ids or set()
        for c in self.clips:
            if getattr(c, 'clip_type', 'preset') != 'preset':
                continue
            if c.id in ignore_ids:
                continue
            if int(getattr(c, 'lane', 0) or 0) != int(lane):
                continue
            if self._preset_overlap(start, length, c.start, c.length):
                return True
        return False

    def _find_auto_lane_for_window(self, start: float, length: float, preferred: Optional[int] = None,
                                   ignore_ids: Optional[set] = None, require_unlocked: bool = True) -> tuple[int, str]:
        ignore_ids = ignore_ids or set()
        lanes = self.lane_count()
        candidates = []
        if preferred is not None:
            candidates.append(max(0, min(self.PRESET_MAX_LANES - 1, int(preferred))))
        for ln in range(lanes):
            if ln not in candidates:
                candidates.append(ln)
        for ln in candidates:
            if require_unlocked and self._is_lane_locked(ln):
                continue
            if not self._preset_overlaps_in_lane(start, length, ln, ignore_ids=ignore_ids):
                reason = "same lane" if preferred == ln else "moved due to overlap"
                return ln, reason
        for ln in range(lanes, self.PRESET_MAX_LANES):
            if require_unlocked and self._is_lane_locked(ln):
                continue
            return ln, "new lane due to overlap"
        fallback = max(0, min(self.PRESET_MAX_LANES - 1, int(preferred or 0)))
        return fallback, "lane cap reached"

    def _normalize_preset_lanes(self) -> None:
        # Clamp lanes to cap first.
        for c in self.clips:
            if getattr(c, 'clip_type', 'preset') == 'preset':
                c.lane = max(0, min(self.PRESET_MAX_LANES - 1, int(getattr(c, 'lane', 0) or 0)))

        used = sorted({c.lane for c in self.clips if getattr(c, 'clip_type', 'preset') == 'preset'})
        if not used:
            used = [0]
        remap = {old: idx for idx, old in enumerate(used)}
        for c in self.clips:
            if getattr(c, 'clip_type', 'preset') == 'preset':
                c.lane = remap.get(c.lane, 0)

        # Compact lane-state table to remove empty lanes.
        new_states: dict[int, dict] = {}
        for old, new in remap.items():
            new_states[new] = dict(self._lane_states.get(old, {'mute': False, 'solo': False, 'lock': False}))
        if 0 not in new_states:
            new_states[0] = {'mute': False, 'solo': False, 'lock': False}
        self._lane_states = new_states

    def _clip_target_meta(self, clip: SongTimelineClip) -> dict:
        return dict(self._preset_target_map.get(getattr(clip, 'preset_id', ''), {}))

    def _clips_conflict_level(self, a: SongTimelineClip, b: SongTimelineClip) -> str:
        key = frozenset((a.id, b.id))
        if key in self._conflict_pairs:
            return self._conflict_pairs[key]
        ma = self._clip_target_meta(a)
        mb = self._clip_target_meta(b)
        ga = set(ma.get('groups', set()) or set())
        gb = set(mb.get('groups', set()) or set())
        fa = set(ma.get('fixtures', set()) or set())
        fb = set(mb.get('fixtures', set()) or set())
        aa = bool(ma.get('all', False))
        bb = bool(mb.get('all', False))
        if aa or bb:
            lvl = 'high'
        elif (ga and gb and ga.intersection(gb)) or (fa and fb and fa.intersection(fb)):
            lvl = 'high'
        elif (ga and gb) or (fa and fb):
            lvl = 'low'
        else:
            lvl = 'none'
        self._conflict_pairs[key] = lvl
        return lvl

    def _refresh_conflict_cache(self) -> None:
        self._conflict_pairs = {}

    def selected_clip(self) -> Optional[SongTimelineClip]:
        if not self._selected_id:
            return None
        for c in self.clips:
            if c.id == self._selected_id:
                return c
        return None

    # ---- drawing ----
    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, False)
        w = self.width()
        h = self.height()
        # Hint to _draw_waveform: only paint columns inside the dirty rect
        # (Qt clips drawing anyway, but skipping the loop is much cheaper).
        try:
            dr = ev.rect()
            self._visible_x_range = (dr.left() - 4, dr.right() + 4)
        except Exception:
            self._visible_x_range = (0, w)
        # backdrop
        p.fillRect(self.rect(), QColor("#141414"))
        # ruler
        p.fillRect(0, 0, w, self.RULER_H, QColor("#1d1d1d"))
        p.setPen(QPen(QColor("#3a3a3a"), 1))
        p.drawLine(0, self.RULER_H, w, self.RULER_H)
        self._draw_ruler(p)
        # waveform
        wf_top = self.RULER_H
        p.fillRect(0, wf_top, w, self.WAVE_H, QColor("#181818"))
        self._draw_waveform(p, wf_top, self.WAVE_H)
        self._draw_trim_markers(p, wf_top, self.WAVE_H)
        # preset clip lane
        lane_top, trigger_lane_top, preset_lane_h, lane_count = self._preset_layout(h)
        p.fillRect(0, lane_top, w, preset_lane_h, QColor("#101010"))
        # Lane separators and lane-state shading.
        for ln in range(lane_count):
            lr = self._lane_rect(ln, lane_top)
            st = self.get_lane_state(ln)
            if st.get('solo'):
                p.fillRect(lr, QColor(36, 70, 46, 55))
            elif st.get('mute'):
                p.fillRect(lr, QColor(70, 36, 36, 55))
            if st.get('lock'):
                p.fillRect(lr, QColor(36, 36, 62, 42))
            if ln > 0:
                y = int(lr.top()) - 1
                p.setPen(QPen(QColor("#202020"), 1))
                p.drawLine(0, y, w, y)
            p.setPen(QPen(QColor("#4f4f4f"), 1))
            p.setFont(QFont("Segoe UI", 7))
            p.drawText(4, int(lr.top()) + 11, f"Lane {ln + 1}")
        # vertical gridlines from ruler
        self._draw_gridlines(p, lane_top, h - lane_top)
        # preset clips
        self._draw_preset_clips(p, lane_top, preset_lane_h)

        # Drag/drop destination preview.
        if self._dnd_preview:
            ln = int(self._dnd_preview.get('lane', 0))
            start = float(self._dnd_preview.get('start', 0.0))
            length = float(self._dnd_preview.get('length', 1.0))
            reason = str(self._dnd_preview.get('reason', '') or '')
            lr = self._lane_rect(ln, lane_top)
            x = int(self.time_to_x(start))
            wv = max(6, int(length * self.pixels_per_sec))
            rr = QRectF(x, lr.top() + self.PRESET_DRAW_PAD_Y, wv,
                        max(8, lr.height() - 2 * self.PRESET_DRAW_PAD_Y))
            p.setPen(QPen(QColor("#d0d0d0"), 2, Qt.PenStyle.DashLine))
            p.setBrush(QBrush(QColor(180, 180, 180, 45)))
            p.drawRect(rr)
            if reason:
                p.setPen(QPen(QColor("#d8d8d8"), 1))
                p.setFont(QFont("Segoe UI", 7, QFont.Weight.Bold))
                p.drawText(QRectF(rr.left() + 4, rr.top() + 2, max(40, rr.width() - 8), 12),
                           Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                           reason)
        # trigger lane
        p.fillRect(0, trigger_lane_top, w, self.TRIGGER_LANE_H, QColor("#0c0c1a"))
        p.setPen(QPen(QColor("#2a2a44"), 1))
        p.drawLine(0, trigger_lane_top, w, trigger_lane_top)
        # lane label
        p.setPen(QPen(QColor("#445566"), 1))
        p.setFont(QFont("Segoe UI", 8))
        p.drawText(4, trigger_lane_top + 12, "MIDI / OSC")
        # trigger clips
        self._draw_trigger_clips(p, trigger_lane_top, self.TRIGGER_LANE_H)
        # playhead
        self._draw_playhead(p, h)
        p.end()

    def _draw_ruler(self, p: QPainter) -> None:
        p.setPen(QPen(QColor("#8a8a8a"), 1))
        p.setFont(QFont("Segoe UI", 8))
        # choose tick step that gives ~80px spacing
        target_px = 80
        step = max(1, int(target_px / max(self.pixels_per_sec, 1)))
        # Snap step to nice values
        for nice in (1, 2, 5, 10, 15, 30, 60, 120, 300):
            if nice >= step:
                step = nice
                break
        t = 0
        while t <= self.duration + 0.001:
            x = int(self.time_to_x(t))
            p.drawLine(x, self.RULER_H - 8, x, self.RULER_H)
            mins = int(t) // 60
            secs = int(t) % 60
            p.drawText(x + 3, self.RULER_H - 10, f"{mins}:{secs:02d}")
            t += step

    def _draw_gridlines(self, p: QPainter, top: int, height: int) -> None:
        p.setPen(QPen(QColor("#1f1f1f"), 1, Qt.PenStyle.SolidLine))
        target_px = 80
        step = max(1, int(target_px / max(self.pixels_per_sec, 1)))
        for nice in (1, 2, 5, 10, 15, 30, 60, 120, 300):
            if nice >= step:
                step = nice
                break
        t = 0
        while t <= self.duration + 0.001:
            x = int(self.time_to_x(t))
            p.drawLine(x, top, x, top + height)
            t += step

    def _draw_waveform(self, p: QPainter, top: int, height: int) -> None:
        if not self.peaks or self.duration <= 0:
            p.setPen(QPen(QColor("#444"), 1))
            p.setFont(QFont("Segoe UI", 9))
            p.drawText(QRectF(0, top, self.width(), height),
                       Qt.AlignmentFlag.AlignCenter,
                       "(waveform building…)" if not self.peaks else "(no audio)")
            return
        mid = top + height // 2
        amp = (height - 6) // 2
        pen = QPen(QColor("#5cb1c9"), 1)
        p.setPen(pen)
        total_w = max(1, int(self.duration * self.pixels_per_sec))
        n = len(self.peaks)
        # Only paint columns inside the current clip region (set by Qt or our
        # _visible_x_range hint from paintEvent). This keeps repaint cost bounded
        # by the viewport size, not the full song length.
        x0, x1 = getattr(self, '_visible_x_range', (0, total_w))
        x0 = max(0, int(x0))
        x1 = min(total_w, int(x1))
        for px in range(x0, x1):
            idx = int(px / total_w * n)
            if idx >= n:
                break
            mn, mx = self.peaks[idx]
            y1 = mid - int(mx * amp)
            y2 = mid - int(mn * amp)
            p.drawLine(px, y1, px, y2)

    def _draw_clips(self, p: QPainter, top: int, height: int) -> None:
        """Legacy alias kept in case external code calls it directly."""
        self._draw_preset_clips(p, top, height)

    def _draw_trim_markers(self, p: QPainter, top: int, height: int) -> None:
        """Shade the trimmed-out regions and draw the trim handles over the
        waveform.  trim_start / trim_end are in seconds; trim_end == 0 means
        'use the natural end' (no trailing trim).
        Both handles are ALWAYS drawn so users can discover and drag them."""
        bottom = top + height
        ts = max(0.0, float(self.trim_start or 0.0))
        te = float(self.trim_end or 0.0) if float(self.trim_end or 0.0) > 0 else self.duration

        ts_x = int(self.time_to_x(ts))
        te_x = int(self.time_to_x(te))

        # Shade trimmed-out regions
        if ts > 0 and ts_x > 0:
            p.fillRect(QRectF(0, top, ts_x, height), QColor(0, 0, 0, 150))
        if self.trim_end > 0 and te < self.duration:
            right = int(self.time_to_x(self.duration))
            if right > te_x:
                p.fillRect(QRectF(te_x, top, right - te_x, height), QColor(0, 0, 0, 150))

        # Helper: format seconds as m:ss.t
        def _fmt(secs: float) -> str:
            m = int(secs) // 60
            s = secs - m * 60
            return f"{m}:{s:05.2f}"

        HANDLE_W = 10
        HANDLE_H = 20
        FLAG_H = 14  # text flag height

        # --- Start handle (green) ---
        ts_col = QColor("#39d27a")
        p.setPen(QPen(ts_col, 2))
        p.drawLine(ts_x, top, ts_x, bottom)
        # Arrow tab pointing right at top of waveform
        tab_ts = QRectF(ts_x, top, HANDLE_W, HANDLE_H)
        p.fillRect(tab_ts, ts_col)
        # Time label
        p.setPen(QPen(QColor("#000000"), 1))
        p.setFont(QFont("Segoe UI", 7, QFont.Weight.Bold))
        p.drawText(QRectF(ts_x + 2, top + 1, 80, FLAG_H), Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                   "▶ " + _fmt(ts))
        # Bottom arrow
        p.setPen(QPen(ts_col, 2))
        p.setBrush(QBrush(ts_col))
        p.drawPolygon(QPointF(ts_x, bottom),
                      QPointF(ts_x - 5, bottom - 8),
                      QPointF(ts_x + 5, bottom - 8))
        p.setBrush(Qt.BrushStyle.NoBrush)

        # --- End handle (orange) ---
        te_col = QColor("#e8864a")
        p.setPen(QPen(te_col, 2))
        p.drawLine(te_x, top, te_x, bottom)
        # Arrow tab pointing left at top of waveform
        tab_te = QRectF(te_x - HANDLE_W, top, HANDLE_W, HANDLE_H)
        p.fillRect(tab_te, te_col)
        # Time label (to the left of handle so it doesn't clip at end)
        p.setPen(QPen(QColor("#000000"), 1))
        p.setFont(QFont("Segoe UI", 7, QFont.Weight.Bold))
        p.drawText(QRectF(te_x - 82, top + 1, 80, FLAG_H),
                   Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter,
                   _fmt(te) + " ◀")
        # Bottom arrow
        p.setPen(QPen(te_col, 2))
        p.setBrush(QBrush(te_col))
        p.drawPolygon(QPointF(te_x, bottom),
                      QPointF(te_x - 5, bottom - 8),
                      QPointF(te_x + 5, bottom - 8))
        p.setBrush(Qt.BrushStyle.NoBrush)


    def _draw_preset_clips(self, p: QPainter, top: int, height: int) -> None:
        # Draw non-selected first so selected clips stay on top.
        ordered = sorted(
            [c for c in self.clips if getattr(c, 'clip_type', 'preset') == 'preset'],
            key=lambda cc: (cc.id in self._selected_ids or cc.id == self._selected_id)
        )

        # Draw conflict tint strips for overlapping clips in the same lane.
        for i, a in enumerate(ordered):
            lane = max(0, min(self.PRESET_MAX_LANES - 1, int(getattr(a, 'lane', 0) or 0)))
            la = self._lane_rect(lane, top)
            ax = int(self.time_to_x(a.start))
            aw = max(2, int(a.length * self.pixels_per_sec))
            for b in ordered[i + 1:]:
                if int(getattr(b, 'lane', 0) or 0) != lane:
                    continue
                if not self._preset_overlap(a.start, a.length, b.start, b.length):
                    continue
                level = self._clips_conflict_level(a, b)
                if level == 'none':
                    continue
                left = max(ax, int(self.time_to_x(b.start)))
                right = min(ax + aw, int(self.time_to_x(b.start) + b.length * self.pixels_per_sec))
                if right <= left:
                    continue
                tint = QColor("#f0b429") if level == 'low' else QColor("#ef4444")
                tint.setAlpha(120 if level == 'low' else 150)
                p.fillRect(QRectF(left, la.top() + 1, right - left, 5), tint)

        for c in ordered:
            if getattr(c, 'clip_type', 'preset') != 'preset':
                continue
            x = int(self.time_to_x(c.start))
            w = max(2, int(c.length * self.pixels_per_sec))
            lane = max(0, min(self.PRESET_MAX_LANES - 1, int(getattr(c, 'lane', 0) or 0)))
            lr = self._lane_rect(lane, top)
            r = QRectF(x, lr.top() + self.PRESET_DRAW_PAD_Y, w,
                       max(8, lr.height() - 2 * self.PRESET_DRAW_PAD_Y))
            base = QColor(c.color or "#4a90e2")
            fill = QColor(base); fill.setAlpha(190)
            if not self.is_clip_audible(c):
                fill = QColor(fill)
                fill.setAlpha(70)
            p.fillRect(r, fill)
            is_sel = (c.id == self._selected_id) or (c.id in self._selected_ids)
            border = QColor("#ffffff") if is_sel else base.darker(150)
            pen_w = 2 if is_sel else 1
            p.setPen(QPen(border, pen_w))
            p.drawRect(r)
            if self._is_lane_locked(lane):
                p.fillRect(QRectF(r.left(), r.top(), r.width(), 10), QColor(60, 60, 95, 120))
            # left/right resize handles
            handle = QColor(0, 0, 0, 90)
            p.fillRect(QRectF(r.left(), r.top(), 4, r.height()), handle)
            p.fillRect(QRectF(r.right() - 4, r.top(), 4, r.height()), handle)

            # Fade visual overlays and drag handles.
            fade_in = max(0.0, min(c.fade_in, c.length))
            fade_out = max(0.0, min(c.fade_out, c.length))
            fin_w = int(fade_in * self.pixels_per_sec)
            fout_w = int(fade_out * self.pixels_per_sec)
            if fin_w > 2:
                path = QPainterPath()
                path.moveTo(r.left(), r.bottom())
                path.lineTo(min(r.right(), r.left() + fin_w), r.bottom())
                path.lineTo(r.left(), r.top())
                path.closeSubpath()
                p.fillPath(path, QColor(255, 255, 255, 35))
            if fout_w > 2:
                path = QPainterPath()
                path.moveTo(r.right(), r.bottom())
                path.lineTo(max(r.left(), r.right() - fout_w), r.bottom())
                path.lineTo(r.right(), r.top())
                path.closeSubpath()
                p.fillPath(path, QColor(255, 255, 255, 35))

            # Fade handles at the bottom edge.
            fh_y = r.bottom() - 6
            p.fillRect(QRectF(r.left() + 6, fh_y, 6, 5), QColor(255, 255, 255, 95))
            p.fillRect(QRectF(r.right() - 12, fh_y, 6, 5), QColor(255, 255, 255, 95))
            # label
            p.setPen(QPen(QColor("#fff"), 1))
            p.setFont(QFont("Segoe UI", 8, QFont.Weight.Bold))
            fm = QFontMetrics(p.font())
            label = fm.elidedText(c.preset_name or "(preset)",
                                  Qt.TextElideMode.ElideRight, int(r.width() - 8))
            p.drawText(QRectF(r.left() + 4, r.top() + 2, r.width() - 8, 16),
                       Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                       label)
            # length text
            p.setFont(QFont("Segoe UI", 7))
            p.setPen(QPen(QColor("#e6e6e6"), 1))
            p.drawText(QRectF(r.left() + 4, r.bottom() - 14, r.width() - 8, 12),
                       Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                       f"{c.length:.2f}s")

    def _draw_trigger_clips(self, p: QPainter, top: int, height: int) -> None:
        """Draw MIDI/OSC trigger clips as fixed-width pills in the trigger lane."""
        pill_w = max(6, int(_TRIGGER_DISPLAY_SEC * self.pixels_per_sec))
        pill_h = height - 16
        for c in self.clips:
            if getattr(c, 'clip_type', 'preset') != 'trigger':
                continue
            x = int(self.time_to_x(c.start))
            r = QRectF(x, top + 8, pill_w, pill_h)
            base = QColor(c.color or "#c97a50")
            fill = QColor(base); fill.setAlpha(200)
            p.setBrush(QBrush(fill))
            is_sel = (c.id == self._selected_id) or (c.id in self._selected_ids)
            border = QColor("#ffffff") if is_sel else base.lighter(160)
            pen_w = 2 if is_sel else 1
            p.setPen(QPen(border, pen_w))
            p.drawRoundedRect(r, 4, 4)
            # icon + label
            p.setPen(QPen(QColor("#fff"), 1))
            p.setFont(QFont("Segoe UI", 7, QFont.Weight.Bold))
            fm = QFontMetrics(p.font())
            label = fm.elidedText(c.preset_name or "📡",
                                  Qt.TextElideMode.ElideRight, pill_w - 4)
            p.drawText(QRectF(r.left() + 2, r.top() + 2, r.width() - 4, r.height() - 4),
                       Qt.AlignmentFlag.AlignCenter | Qt.TextFlag.TextWordWrap,
                       label)

    def _draw_playhead(self, p: QPainter, h: int) -> None:
        x = int(self.time_to_x(self.playhead))
        p.setPen(QPen(QColor("#ff5050"), 2))
        p.drawLine(x, 0, x, h)
        # cap
        p.setBrush(QBrush(QColor("#ff5050")))
        p.drawPolygon(QPointF(x, 0), QPointF(x - 6, 10), QPointF(x + 6, 10))

    # ---- hit testing ----
    def _hit_clip(self, x: float, y: float):
        """Return (clip, mode) where mode is move/resize/fade operations, or (None, None)."""
        lane_top, trigger_lane_top, _preset_h, lane_count = self._preset_layout(self.height())
        if y < lane_top:
            return None, None

        # Check trigger lane first (bottom band)
        if y >= trigger_lane_top:
            pill_w = max(6, int(_TRIGGER_DISPLAY_SEC * self.pixels_per_sec))
            for c in reversed(self.clips):
                if getattr(c, 'clip_type', 'preset') != 'trigger':
                    continue
                cx = self.time_to_x(c.start)
                if cx <= x <= cx + pill_w:
                    return c, 'move'  # triggers are always move-only
            return None, None

        # Preset clip lane
        for c in reversed(self.clips):
            if getattr(c, 'clip_type', 'preset') != 'preset':
                continue
            lane = max(0, int(getattr(c, 'lane', 0) or 0))
            if lane != self._lane_for_y(y, lane_top, lane_count):
                continue
            cx = self.time_to_x(c.start)
            cw = max(2, c.length * self.pixels_per_sec)
            if cx <= x <= cx + cw:
                # Bottom-corner fade handles.
                lr = self._lane_rect(lane, lane_top)
                ry = lr.top() + self.PRESET_DRAW_PAD_Y
                rh = max(8, lr.height() - 2 * self.PRESET_DRAW_PAD_Y)
                if (ry + rh - 9) <= y <= (ry + rh + 1):
                    if cx + 4 <= x <= cx + 16:
                        return c, 'fade_in'
                    if (cx + cw - 16) <= x <= (cx + cw - 4):
                        return c, 'fade_out'
                if x - cx <= 6:
                    return c, 'resize_l'
                if cx + cw - x <= 6:
                    return c, 'resize_r'
                return c, 'move'
        return None, None

    def _hit_trim_handle(self, x: float, y: float) -> Optional[str]:
        """Return 'trim_start'|'trim_end' if (x,y) is within the trim handle grab zone, else None."""
        top = self.RULER_H
        bottom = self.RULER_H + self.WAVE_H
        if not (top <= y <= bottom):
            return None
        TOL = 10  # wider tolerance to match larger handles
        te = self.trim_end if self.trim_end > 0 else self.duration
        ts_x = self.time_to_x(self.trim_start)
        te_x = self.time_to_x(te)
        # Check end first — if handles overlap, end takes priority (drag left to unset)
        if abs(x - te_x) <= TOL:
            return 'trim_end'
        if abs(x - ts_x) <= TOL:
            return 'trim_start'
        return None

    # ---- mouse / keyboard ----
    def mousePressEvent(self, ev):
        x, y = ev.position().x(), ev.position().y()
        if y < self.RULER_H:
            # seek on ruler click
            self.playhead = max(0.0, min(self.duration, self.x_to_time(x)))
            self._drag_mode = 'seek'
            self.update()
            self.selectionChanged.emit(None)
            return
        # Trim handle drag has priority over clip interaction.
        if ev.button() == Qt.MouseButton.LeftButton:
            trim_hit = self._hit_trim_handle(x, y)
            if trim_hit:
                self._trim_drag = trim_hit
                return
        mods = ev.modifiers()
        ctrl = bool(mods & Qt.KeyboardModifier.ControlModifier)
        shift = bool(mods & Qt.KeyboardModifier.ShiftModifier)
        clip, mode = self._hit_clip(x, y)
        if clip:
            clip_lane = int(getattr(clip, 'lane', 0) or 0)
            if self._is_lane_locked(clip_lane) and mode in ('move', 'resize_l', 'resize_r', 'fade_in', 'fade_out'):
                # Keep selection behavior, but refuse edits on locked lanes.
                self._selected_id = clip.id
                self._selected_ids = {clip.id}
                self.selectionChanged.emit(clip)
                self.update()
                return
            if ctrl:
                # Toggle this clip in the multi-selection.
                if clip.id in self._selected_ids:
                    self._selected_ids.discard(clip.id)
                    if self._selected_id == clip.id:
                        self._selected_id = next(iter(self._selected_ids), None)
                else:
                    self._selected_ids.add(clip.id)
                    self._selected_id = clip.id
            elif shift and self._selected_id:
                # Range-select from anchor to clicked clip by start time.
                anchor = next((c for c in self.clips if c.id == self._selected_id), None)
                if anchor is not None:
                    lo, hi = sorted([anchor.start, clip.start])
                    for cc in self.clips:
                        if lo - 1e-6 <= cc.start <= hi + 1e-6:
                            self._selected_ids.add(cc.id)
                self._selected_ids.add(clip.id)
                self._selected_id = clip.id
            else:
                # Simple click: if clicked clip is part of multi-selection,
                # keep the group for group-drag; otherwise replace selection.
                if clip.id not in self._selected_ids:
                    self._selected_ids = {clip.id}
                self._selected_id = clip.id
            self._drag_mode = mode
            self._drag_clip = clip
            self._drag_grab_dx = x - self.time_to_x(clip.start)
            self._drag_original = (clip.start, clip.length, clip.fade_in, clip.fade_out)
            # Build group offsets for multi-clip move (only for 'move' mode;
            # resize handles operate on the single clip).
            self._drag_group_offsets = {}
            if mode == 'move' and len(self._selected_ids) > 1:
                for cc in self.clips:
                    if cc.id in self._selected_ids and cc.id != clip.id:
                        self._drag_group_offsets[cc.id] = cc.start - clip.start
            self._move_preview_lane = None
            self._move_preview_reason = ""
            self.selectionChanged.emit(clip)
            self.update()
        else:
            if not (ctrl or shift):
                self._selected_id = None
                self._selected_ids.clear()
            self._drag_mode = None
            self._drag_clip = None
            self.selectionChanged.emit(self.selected_clip())
            self.update()

    def mouseMoveEvent(self, ev):
        x = ev.position().x()
        y = ev.position().y()
        # Trim handle drag
        if self._trim_drag:
            t = max(0.0, min(self.duration, self.x_to_time(x)))
            if self._trim_drag == 'trim_start':
                te = self.trim_end if self.trim_end > 0 else self.duration
                self.trim_start = max(0.0, min(te - 0.1, t))
            else:  # trim_end
                te_val = max(self.trim_start + 0.1, t)
                # Snap to natural end when dragged within 0.3s of duration
                if te_val >= self.duration - 0.3:
                    self.trim_end = 0.0
                else:
                    self.trim_end = min(self.duration, te_val)
            self.update()
            return
        if self._drag_mode == 'seek':
            self.playhead = max(0.0, min(self.duration, self.x_to_time(x)))
            self.update()
            return
        if not self._drag_clip:
            # update cursor + hover tooltip
            # Check trim handles first
            trim_hit = self._hit_trim_handle(x, ev.position().y())
            if trim_hit:
                self.setCursor(Qt.CursorShape.SizeHorCursor)
                self.setToolTip(
                    "Trim start — drag to skip leading silence (green handle)"
                    if trim_hit == 'trim_start' else
                    "Trim end — drag to cut trailing silence (orange handle)\n"
                    "Drag to end of song to remove trim"
                )
                return
            hit_clip, mode = self._hit_clip(x, ev.position().y())
            if mode in ('resize_l', 'resize_r', 'fade_in', 'fade_out'):
                self.setCursor(Qt.CursorShape.SizeHorCursor)
            elif mode == 'move':
                self.setCursor(Qt.CursorShape.SizeAllCursor)
            else:
                self.setCursor(Qt.CursorShape.ArrowCursor)
            # Tooltip with preset name + timing for the clip under the mouse
            if hit_clip is not None:
                end_t = hit_clip.start + hit_clip.length
                tip = (f"<b>{(hit_clip.preset_name or '(preset)')}</b><br>"
                       f"Start: {hit_clip.start:.2f}s<br>"
                       f"Length: {hit_clip.length:.2f}s "
                       f"(ends {end_t:.2f}s)<br>"
                       f"Fade in/out: {hit_clip.fade_in:.2f}s / "
                       f"{hit_clip.fade_out:.2f}s")
                self.setToolTip(tip)
            else:
                self.setToolTip("")
            return
        c = self._drag_clip
        t = self.x_to_time(x)
        if self._drag_mode == 'move':
            new_start = max(0.0, t - self._drag_grab_dx / self.pixels_per_sec)
            new_start = min(new_start, max(0.0, self.duration - c.length))
            lane_top, _trigger_top, _ph, lanes = self._preset_layout(self.height())
            preferred_lane = self._lane_for_y(y, lane_top, lanes)
            ignore = set(self._selected_ids) if self._drag_group_offsets else {c.id}
            lane, reason = self._find_auto_lane_for_window(
                new_start, c.length, preferred=preferred_lane, ignore_ids=ignore, require_unlocked=True
            )
            c.start = new_start
            c.lane = lane
            self._move_preview_lane = lane
            self._move_preview_reason = reason
            # Move grouped clips by the same delta, clamped to bounds.
            if self._drag_group_offsets:
                by_id = {cc.id: cc for cc in self.clips}
                for cid, off in self._drag_group_offsets.items():
                    other = by_id.get(cid)
                    if other is None:
                        continue
                    if self._is_lane_locked(int(getattr(other, 'lane', 0) or 0)):
                        continue
                    other_start = max(0.0,
                                      min(self.duration - other.length,
                                          new_start + off))
                    olane, _ = self._find_auto_lane_for_window(
                        other_start, other.length, preferred=lane,
                        ignore_ids=ignore, require_unlocked=True
                    )
                    other.start = other_start
                    other.lane = olane
        elif self._drag_mode == 'resize_l':
            new_start = max(0.0, t)
            new_start = min(new_start, c.start + c.length - 0.05)
            delta = new_start - c.start
            c.start = new_start
            c.length = max(0.05, c.length - delta)
        elif self._drag_mode == 'resize_r':
            new_len = max(0.05, t - c.start)
            new_len = min(new_len, max(0.05, self.duration - c.start))
            c.length = new_len
        elif self._drag_mode == 'fade_in':
            c.fade_in = max(0.0, min(c.length, t - c.start))
        elif self._drag_mode == 'fade_out':
            c.fade_out = max(0.0, min(c.length, (c.start + c.length) - t))
        if c.fade_in + c.fade_out > c.length:
            over = c.fade_in + c.fade_out - c.length
            if self._drag_mode == 'fade_in':
                c.fade_out = max(0.0, c.fade_out - over)
            elif self._drag_mode == 'fade_out':
                c.fade_in = max(0.0, c.fade_in - over)
        self._refresh_conflict_cache()
        self.update()
        self.changed.emit()

    def mouseReleaseEvent(self, ev):
        if self._trim_drag:
            self._trim_drag = None
            self.trimChanged.emit(self.trim_start, self.trim_end)
            return
        self._drag_mode = None
        self._drag_clip = None
        self._drag_original = None
        self._drag_group_offsets = {}
        self._move_preview_lane = None
        self._move_preview_reason = ""
        self._normalize_preset_lanes()
        self._refresh_conflict_cache()
        self._refresh_minimum_height()
        self.updateGeometry()
        self.update()

    # ---- context menu ----
    def contextMenuEvent(self, ev):
        x, y = ev.pos().x(), ev.pos().y()
        clip, _ = self._hit_clip(x, y)
        menu = QMenu(self)
        if clip:
            # If user right-clicks a clip that isn't part of the current
            # multi-selection, replace the selection with that clip.
            if clip.id not in self._selected_ids:
                self._selected_id = clip.id
                self._selected_ids = {clip.id}
                self.selectionChanged.emit(clip)
                self.update()
            n = len(self._selected_ids)
            sel_word = f"{n} Clips" if n > 1 else "Clip"
            menu.addAction(f"Cut {sel_word}\tCtrl+X", self._cut_selected)
            menu.addAction(f"Copy {sel_word}\tCtrl+C", self._copy_selected)
            menu.addAction("Paste at Playhead\tCtrl+V", self._paste_at_playhead)
            menu.addSeparator()
            menu.addAction(f"Duplicate {sel_word}\tCtrl+D", self._duplicate_selected)
            menu.addSeparator()
            menu.addAction(f"Delete {sel_word}\tDel", self._delete_selected)
        else:
            menu.addAction("Paste at Playhead\tCtrl+V", self._paste_at_playhead)
        menu.exec(ev.globalPos())

    # ---- clipboard / edit ops ----
    def _selected_clips_in_order(self) -> list:
        """All currently-selected clips, sorted by start time."""
        sel = [c for c in self.clips if c.id in self._selected_ids]
        if not sel and self._selected_id:
            sel = [c for c in self.clips if c.id == self._selected_id]
        sel.sort(key=lambda c: c.start)
        return sel

    def _copy_selected(self):
        sel = self._selected_clips_in_order()
        if not sel:
            return
        self._clipboard_multi = [c.to_dict() for c in sel]
        # Keep legacy single-clip slot for backward compatibility.
        self._clipboard = self._clipboard_multi[0] if self._clipboard_multi else None

    def _cut_selected(self):
        sel = self._selected_clips_in_order()
        if not sel:
            return
        sel = [c for c in sel if not (getattr(c, 'clip_type', 'preset') == 'preset' and self._is_lane_locked(int(getattr(c, 'lane', 0) or 0)))]
        if not sel:
            return
        self._clipboard_multi = [c.to_dict() for c in sel]
        self._clipboard = self._clipboard_multi[0]
        for c in sel:
            try:
                self.clips.remove(c)
            except ValueError:
                pass
        self._selected_id = None
        self._selected_ids.clear()
        self._normalize_preset_lanes()
        self._refresh_conflict_cache()
        self._refresh_minimum_height()
        self.updateGeometry()
        self.selectionChanged.emit(None)
        self.update()
        self.changed.emit()

    def _paste_at_playhead(self):
        clips_data = self._clipboard_multi or (
            [self._clipboard] if self._clipboard else [])
        if not clips_data:
            return
        # Preserve relative spacing between pasted clips by anchoring to
        # the earliest start time in the clipboard.
        base = min((d.get('start', 0.0) for d in clips_data), default=0.0)
        anchor = max(0.0, self.playhead)
        new_clips = []
        for d in clips_data:
            n = SongTimelineClip.from_dict(d)
            n.id = str(uuid.uuid4())
            offset = d.get('start', 0.0) - base
            n.start = max(0.0,
                          min(self.duration - n.length, anchor + offset))
            if getattr(n, 'clip_type', 'preset') == 'preset':
                lane, _ = self._find_auto_lane_for_window(n.start, n.length, preferred=n.lane, ignore_ids=None)
                n.lane = lane
            self.clips.append(n)
            new_clips.append(n)
        self._normalize_preset_lanes()
        self._refresh_conflict_cache()
        self._refresh_minimum_height()
        self.updateGeometry()
        self._selected_ids = {n.id for n in new_clips}
        self._selected_id = new_clips[-1].id if new_clips else None
        self.selectionChanged.emit(self.selected_clip())
        self.update()
        self.changed.emit()

    def _duplicate_selected(self):
        """Duplicate the current selection and append immediately after the
        last selected clip (handy keyboard-driven workflow)."""
        sel = self._selected_clips_in_order()
        if not sel:
            return
        base = sel[0].start
        last_end = max(c.start + c.length for c in sel)
        anchor = min(self.duration, last_end)
        new_clips = []
        for c in sel:
            if getattr(c, 'clip_type', 'preset') == 'preset' and self._is_lane_locked(int(getattr(c, 'lane', 0) or 0)):
                continue
            n = SongTimelineClip.from_dict(c.to_dict())
            n.id = str(uuid.uuid4())
            offset = c.start - base
            n.start = max(0.0,
                          min(self.duration - n.length, anchor + offset))
            if getattr(n, 'clip_type', 'preset') == 'preset':
                lane, _ = self._find_auto_lane_for_window(n.start, n.length, preferred=n.lane, ignore_ids=None)
                n.lane = lane
            self.clips.append(n)
            new_clips.append(n)
        if not new_clips:
            return
        self._normalize_preset_lanes()
        self._refresh_conflict_cache()
        self._refresh_minimum_height()
        self.updateGeometry()
        self._selected_ids = {n.id for n in new_clips}
        self._selected_id = new_clips[-1].id if new_clips else None
        self.selectionChanged.emit(self.selected_clip())
        self.update()
        self.changed.emit()

    def _delete_selected(self):
        sel = self._selected_clips_in_order()
        if not sel:
            return
        sel = [c for c in sel if not (getattr(c, 'clip_type', 'preset') == 'preset' and self._is_lane_locked(int(getattr(c, 'lane', 0) or 0)))]
        if not sel:
            return
        for c in sel:
            try:
                self.clips.remove(c)
            except ValueError:
                pass
        self._normalize_preset_lanes()
        self._refresh_conflict_cache()
        self._refresh_minimum_height()
        self.updateGeometry()
        self._selected_id = None
        self._selected_ids.clear()
        self.selectionChanged.emit(None)
        self.update()
        self.changed.emit()

    # ---- drag and drop from preset list ----
    def dragEnterEvent(self, ev):
        if ev.mimeData().hasFormat(_PRESET_MIME):
            ev.acceptProposedAction()

    def dragMoveEvent(self, ev):
        if ev.mimeData().hasFormat(_PRESET_MIME):
            try:
                payload = json.loads(bytes(ev.mimeData().data(_PRESET_MIME)).decode('utf-8'))
            except Exception:
                payload = {}
            t = max(0.0, min(self.duration, self.x_to_time(ev.position().x())))
            lane_top, _trigger_top, _ph, lanes = self._preset_layout(self.height())
            preferred_lane = self._lane_for_y(ev.position().y(), lane_top, lanes)
            is_trigger = bool(payload.get("is_trigger", False))
            if is_trigger:
                preview_lane = 0
                reason = "trigger lane"
                length = _TRIGGER_DISPLAY_SEC
            else:
                length = min(4.0, max(0.5, self.duration - t))
                preview_lane, reason = self._find_auto_lane_for_window(
                    t, length, preferred=preferred_lane, ignore_ids=None, require_unlocked=True
                )
            self._dnd_preview = {
                'lane': preview_lane,
                'start': t,
                'length': length,
                'reason': reason,
            }
            self.update()
            ev.acceptProposedAction()

    def dragLeaveEvent(self, ev):
        self._dnd_preview = None
        self.update()
        super().dragLeaveEvent(ev)

    def dropEvent(self, ev):
        if not ev.mimeData().hasFormat(_PRESET_MIME):
            return
        try:
            payload = json.loads(bytes(ev.mimeData().data(_PRESET_MIME)).decode('utf-8'))
        except Exception:
            self._dnd_preview = None
            self.update()
            return
        x = ev.position().x()
        t = max(0.0, min(self.duration, self.x_to_time(x)))
        is_trigger = bool(payload.get("is_trigger", False))
        if is_trigger:
            clip = SongTimelineClip.make(
                preset_id=payload.get("id", ""),
                preset_name=payload.get("name", ""),
                start=t,
                length=_TRIGGER_DISPLAY_SEC,
                color=payload.get("color", "#c97a50") or "#c97a50",
                clip_type="trigger",
            )
        else:
            lane_top, _trigger_top, _ph, lanes = self._preset_layout(self.height())
            preferred_lane = self._lane_for_y(ev.position().y(), lane_top, lanes)
            clip_len = min(4.0, max(0.5, self.duration - t))
            lane, _reason = self._find_auto_lane_for_window(
                t, clip_len, preferred=preferred_lane, ignore_ids=None, require_unlocked=True
            )
            clip = SongTimelineClip.make(
                preset_id=payload.get("id", ""),
                preset_name=payload.get("name", ""),
                start=t,
                length=clip_len,
                color=payload.get("color", "#4a90e2") or "#4a90e2",
                clip_type="preset",
            )
            clip.lane = lane
            # Seed sensible per-preset defaults.
            if clip.preset_id == _BUILTIN_OVERLAY_SET_PCT:
                clip.params['overlay_pct'] = 50.0
        self.clips.append(clip)
        self._normalize_preset_lanes()
        self._refresh_conflict_cache()
        self._refresh_minimum_height()
        self.updateGeometry()
        self._selected_id = clip.id
        self._selected_ids = {clip.id}
        self.selectionChanged.emit(clip)
        self._dnd_preview = None
        self.update()
        self.changed.emit()
        ev.acceptProposedAction()


# ---------------------------------------------------------------------------
#  Editor dialog
# ---------------------------------------------------------------------------

class SongTimelineEditor(QDialog):
    """Modeless-friendly dialog for editing one song's timeline."""

    def __init__(self, gui, item, parent=None):
        super().__init__(parent or gui)
        self.gui = gui
        self.item = item
        self.setWindowTitle(f"Timeline — {item.name}")
        self.resize(1180, 640)
        self.setStyleSheet("""
            QDialog { background: #1a1a1a; color: #ddd; }
            QLabel { color: #ccc; }
            QPushButton { background: #2d2d2d; color: #fff; border: 1px solid #3a3a3a;
                          border-radius: 4px; padding: 5px 10px; }
            QPushButton:hover { background: #3a3a3a; }
            QPushButton:pressed { background: #555; }
            QLineEdit, QDoubleSpinBox { background: #232323; color: #fff;
                                         border: 1px solid #3a3a3a; padding: 3px;
                                         border-radius: 3px; }
        """)

        self.tl: SongTimeline = load_timeline(gui, item)
        self._dirty = False
        self._preview_active_clips: dict = {}
        self._preview_player = None  # _VideoAudioPlayer instance
        self._preview_position: float = 0.0  # tracked by ptimer
        self._preview_start_wall: float = 0.0  # time.monotonic() when play started
        self._preview_start_pos: float = 0.0   # playhead pos when play started
        self._playing = False
        # Live preset preview (right-click → Preview Effect)
        self._previewing_preset_id: Optional[str] = None
        self._preview_layer_eids: list = []
        # Undo / redo stack — list[dict] snapshots of clips
        self._undo_stack: list = []
        self._redo_stack: list = []
        self._suspend_history: bool = False
        self._did_initial_fit_zoom: bool = False
        # NDI video push during timeline play
        self._ndi_video_active: bool = False
        self._viz_audio_muted_prev = None  # saved state to restore

        self._build_ui()
        self._install_shortcuts()
        self._load_waveform_async()
        # Seed undo history with the initial state so the first edit can be undone.
        self._undo_stack.append(self._snapshot_clips())

    # ---- UI ----
    def _build_ui(self) -> None:
        root = QVBoxLayout(self)
        root.setContentsMargins(8, 8, 8, 8)
        root.setSpacing(6)

        # Transport
        bar = QHBoxLayout()
        self.btn_play = QPushButton("▶ Play")
        self.btn_play.clicked.connect(self._toggle_play)
        self.btn_stop = QPushButton("■ Stop")
        self.btn_stop.clicked.connect(self._stop_preview)
        self.btn_rewind = QPushButton("⏮ Rewind")
        self.btn_rewind.clicked.connect(self._rewind)
        self.lbl_time = QLabel("0:00.0 / 0:00.0")
        self.lbl_time.setStyleSheet("font-family: Consolas; font-size: 12pt; color: #fff;")
        bar.addWidget(self.btn_rewind)
        bar.addWidget(self.btn_play)
        bar.addWidget(self.btn_stop)
        bar.addSpacing(20)
        bar.addWidget(self.lbl_time)
        bar.addStretch(1)
        bar.addWidget(QLabel("Zoom"))
        self.btn_zoom_out = QPushButton("−"); self.btn_zoom_out.setFixedWidth(28)
        self.btn_zoom_in = QPushButton("+");  self.btn_zoom_in.setFixedWidth(28)
        self.btn_zoom_out.clicked.connect(lambda: self._zoom(0.75))
        self.btn_zoom_in.clicked.connect(lambda: self._zoom(1.33))
        bar.addWidget(self.btn_zoom_out)
        bar.addWidget(self.btn_zoom_in)
        root.addLayout(bar)

        # Lane controls
        lane_bar = QHBoxLayout()
        lane_bar.addWidget(QLabel("Lanes:"))
        self._lane_controls = []
        for i in range(_TimelineCanvas.PRESET_MAX_LANES):
            wrap = QWidget()
            row = QHBoxLayout(wrap)
            row.setContentsMargins(0, 0, 0, 0)
            row.setSpacing(4)
            lbl = QLabel(f"{i + 1}")
            lbl.setStyleSheet("color:#9aa0a6; min-width:16px; font-weight:600;")
            btn_m = QPushButton("Mute")
            btn_s = QPushButton("Solo")
            btn_l = QPushButton("Lock")
            for b in (btn_m, btn_s, btn_l):
                b.setCheckable(True)
                b.setMinimumSize(52, 26)
                b.setToolTip("Lane control")
                b.setStyleSheet(
                    "QPushButton {"
                    "  padding: 3px 8px;"
                    "  font-size: 11px;"
                    "  font-weight: 600;"
                    "}"
                )
            btn_m.clicked.connect(lambda checked, lane=i: self._set_lane_state(lane, 'mute', checked))
            btn_s.clicked.connect(lambda checked, lane=i: self._set_lane_state(lane, 'solo', checked))
            btn_l.clicked.connect(lambda checked, lane=i: self._set_lane_state(lane, 'lock', checked))
            row.addWidget(lbl)
            row.addWidget(btn_m)
            row.addWidget(btn_s)
            row.addWidget(btn_l)
            lane_bar.addWidget(wrap)
            self._lane_controls.append((wrap, btn_m, btn_s, btn_l))
        lane_bar.addStretch(1)
        root.addLayout(lane_bar)

        # Splitter: presets | timeline area
        split = QSplitter(Qt.Orientation.Horizontal)

        # Left: preset list
        left = QWidget()
        lv = QVBoxLayout(left); lv.setContentsMargins(0, 0, 0, 0); lv.setSpacing(4)
        lv.addWidget(QLabel("Presets — drag onto timeline"))
        self.search = QLineEdit()
        self.search.setPlaceholderText("Filter…")
        self.search.textChanged.connect(lambda s: self.preset_list.refresh(s))
        lv.addWidget(self.search)
        self.preset_list = _PresetListWidget(self.gui)
        # Wire live-preview actions from the preset list to the editor.
        self.preset_list.previewRequested.connect(self._start_preset_preview)
        self.preset_list.stopPreviewRequested.connect(self._stop_preset_preview)
        self.preset_list.interactionStarted.connect(self._on_preset_interaction)
        lv.addWidget(self.preset_list, 1)
        split.addWidget(left)

        # Right: scroll area with canvas + clip inspector below
        right = QWidget()
        rv = QVBoxLayout(right); rv.setContentsMargins(0, 0, 0, 0); rv.setSpacing(4)

        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(False)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.canvas = _TimelineCanvas()
        self.canvas.clips = list(self.tl.clips)
        self.canvas.duration = max(self.tl.duration, 60.0)
        # Load per-item trim points from the VisualizerItem so they appear
        # as draggable handles on the waveform immediately on open.
        self.canvas.trim_start = float(getattr(self.item, 'trim_start', 0.0) or 0.0)
        self.canvas.trim_end = float(getattr(self.item, 'trim_end', 0.0) or 0.0)
        self.canvas.selectionChanged.connect(self._on_selection)
        self.canvas.changed.connect(self._on_canvas_changed)
        self.canvas.trimChanged.connect(self._on_trim_changed)
        self.scroll.setWidget(self.canvas)
        self.canvas.set_preset_target_map(self._build_preset_target_map())
        rv.addWidget(self.scroll, 1)

        # Inspector
        insp = QHBoxLayout()
        insp.addWidget(QLabel("Selected — Start:"))
        self.sp_start = QDoubleSpinBox(); self.sp_start.setRange(0, 100000); self.sp_start.setDecimals(2)
        self.sp_start.setSingleStep(0.1); self.sp_start.setSuffix(" s")
        self.sp_start.valueChanged.connect(self._inspector_apply)
        insp.addWidget(self.sp_start)
        insp.addSpacing(10)
        insp.addWidget(QLabel("Length:"))
        self.sp_len = QDoubleSpinBox(); self.sp_len.setRange(0.05, 100000); self.sp_len.setDecimals(2)
        self.sp_len.setSingleStep(0.1); self.sp_len.setSuffix(" s")
        self.sp_len.valueChanged.connect(self._inspector_apply)
        insp.addWidget(self.sp_len)
        insp.addSpacing(10)
        insp.addWidget(QLabel("Fade In:"))
        self.sp_fin = QDoubleSpinBox(); self.sp_fin.setRange(0, 60); self.sp_fin.setDecimals(2); self.sp_fin.setSuffix(" s")
        self.sp_fin.valueChanged.connect(self._inspector_apply)
        insp.addWidget(self.sp_fin)
        insp.addWidget(QLabel("Fade Out:"))
        self.sp_fout = QDoubleSpinBox(); self.sp_fout.setRange(0, 60); self.sp_fout.setDecimals(2); self.sp_fout.setSuffix(" s")
        self.sp_fout.valueChanged.connect(self._inspector_apply)
        insp.addWidget(self.sp_fout)
        # Overlay-% spinbox — only relevant for the built-in "Video Overlay:
        # SET %" preset. Hidden for everything else.
        self.lbl_overlay_pct = QLabel("Overlay %:")
        self.sp_overlay_pct = QDoubleSpinBox()
        self.sp_overlay_pct.setRange(0, 100)
        self.sp_overlay_pct.setDecimals(0)
        self.sp_overlay_pct.setSingleStep(5)
        self.sp_overlay_pct.setSuffix(" %")
        self.sp_overlay_pct.valueChanged.connect(self._inspector_apply)
        insp.addWidget(self.lbl_overlay_pct)
        insp.addWidget(self.sp_overlay_pct)
        self.lbl_overlay_pct.setVisible(False)
        self.sp_overlay_pct.setVisible(False)
        insp.addStretch(1)
        self.btn_del = QPushButton("Delete Selected")
        self.btn_del.clicked.connect(self.canvas._delete_selected)
        insp.addWidget(self.btn_del)
        rv.addLayout(insp)
        self._set_inspector_enabled(False)
        self._refresh_lane_controls()

        # Trim row — always visible below inspector
        trim_row = QHBoxLayout()
        trim_row.addWidget(QLabel("▶ Song Start:"))
        self.sp_trim_start = QDoubleSpinBox()
        self.sp_trim_start.setRange(0.0, 100000.0)
        self.sp_trim_start.setDecimals(2)
        self.sp_trim_start.setSingleStep(0.5)
        self.sp_trim_start.setSuffix(" s")
        self.sp_trim_start.setToolTip("Song start offset — audio/video skips this many seconds at the beginning")
        self.sp_trim_start.setValue(float(getattr(self.item, 'trim_start', 0.0) or 0.0))
        self.sp_trim_start.valueChanged.connect(self._on_trim_spinbox_changed)
        trim_row.addWidget(self.sp_trim_start)
        trim_row.addSpacing(14)
        trim_row.addWidget(QLabel("◀ Song End (0 = natural end):"))
        self.sp_trim_end = QDoubleSpinBox()
        self.sp_trim_end.setRange(0.0, 100000.0)
        self.sp_trim_end.setDecimals(2)
        self.sp_trim_end.setSingleStep(0.5)
        self.sp_trim_end.setSuffix(" s")
        self.sp_trim_end.setToolTip("Song end time — 0 means play to the natural end of the file")
        self.sp_trim_end.setValue(float(getattr(self.item, 'trim_end', 0.0) or 0.0))
        self.sp_trim_end.valueChanged.connect(self._on_trim_spinbox_changed)
        trim_row.addWidget(self.sp_trim_end)
        trim_row.addSpacing(6)
        btn_trim_reset = QPushButton("Reset Trim")
        btn_trim_reset.setToolTip("Reset start to 0 and end to natural end")
        btn_trim_reset.clicked.connect(self._reset_trim)
        trim_row.addWidget(btn_trim_reset)
        trim_row.addSpacing(20)
        trim_row.addWidget(QLabel("🔊 Volume:"))
        from PyQt6.QtWidgets import QSpinBox as _QSpinBox
        self.sp_volume = _QSpinBox()
        self.sp_volume.setRange(0, 100)
        self.sp_volume.setSuffix(" %")
        self.sp_volume.setSingleStep(5)
        self.sp_volume.setToolTip("Per-song volume — scales audio on top of the global video volume")
        self.sp_volume.setValue(int(getattr(self.item, 'volume', 100)))
        self.sp_volume.valueChanged.connect(self._on_volume_spinbox_changed)
        trim_row.addWidget(self.sp_volume)
        trim_row.addStretch(1)
        rv.addLayout(trim_row)

        split.addWidget(right)
        split.setSizes([220, 940])
        root.addWidget(split, 1)

        # Footer
        foot = QHBoxLayout()
        self.lbl_hint = QLabel(
            "Drag preset onto lane • Drag clip / handles to move/resize • "
            "Bottom edge handles = fade in/out • "
            "Green ▶ / Orange ◀ handles on waveform = drag start/end time • "
            "Ctrl/Shift+click for multi-select • Ctrl+C/V/X/D • Ctrl+Z/Y undo • "
            "Right-click preset → Preview"
        )
        self.lbl_hint.setStyleSheet("color:#888; font-size: 9pt;")
        foot.addWidget(self.lbl_hint, 1)
        self.btn_save = QPushButton("Save")
        self.btn_save.clicked.connect(self._save)
        self.btn_close = QPushButton("Save && Close")
        self.btn_close.clicked.connect(self._save_and_close)
        foot.addWidget(self.btn_save)
        foot.addWidget(self.btn_close)
        root.addLayout(foot)

        # Polling timer for playhead/preview
        self._ptimer = QTimer(self)
        self._ptimer.setInterval(33)
        self._ptimer.timeout.connect(self._tick_preview)

    def _install_shortcuts(self) -> None:
        def add(seq: str, fn):
            sc = QShortcut(QKeySequence(seq), self)
            sc.setContext(Qt.ShortcutContext.WindowShortcut)
            sc.activated.connect(fn)
        add("Ctrl+C", self.canvas._copy_selected)
        add("Ctrl+X", self.canvas._cut_selected)
        add("Ctrl+V", self.canvas._paste_at_playhead)
        add("Ctrl+D", self.canvas._duplicate_selected)
        add("Ctrl+A", self._select_all_clips)
        add("Delete", self.canvas._delete_selected)
        add("Space",  self._toggle_play)
        add("Ctrl+Z", self._undo)
        add("Ctrl+Y", self._redo)
        add("Ctrl+Shift+Z", self._redo)

    def _select_all_clips(self) -> None:
        self.canvas._selected_ids = {c.id for c in self.canvas.clips}
        self.canvas._selected_id = next(iter(self.canvas._selected_ids), None)
        self.canvas.selectionChanged.emit(self.canvas.selected_clip())
        self.canvas.update()

    # ---- undo / redo --------------------------------------------------
    def _snapshot_clips(self) -> list:
        return [c.to_dict() for c in self.canvas.clips]

    def _restore_clips(self, snap: list) -> None:
        self.canvas.clips = [SongTimelineClip.from_dict(d) for d in snap]
        self.canvas._normalize_preset_lanes()
        self.canvas._refresh_conflict_cache()
        self.canvas._refresh_minimum_height()
        self.canvas.updateGeometry()
        # Drop selections that no longer exist.
        valid = {c.id for c in self.canvas.clips}
        self.canvas._selected_ids = {i for i in self.canvas._selected_ids if i in valid}
        if self.canvas._selected_id not in valid:
            self.canvas._selected_id = next(iter(self.canvas._selected_ids), None)
        self.canvas.update()
        self.canvas.selectionChanged.emit(self.canvas.selected_clip())

    def _push_history(self) -> None:
        """Record the *current* clip state into the undo stack. Call this
        AFTER a change has been applied (the canvas.changed signal fires
        after every edit op)."""
        if self._suspend_history:
            return
        snap = self._snapshot_clips()
        # Coalesce identical consecutive snapshots (e.g. mouse-drag emitting
        # many changes with no real difference at the end).
        if self._undo_stack and self._undo_stack[-1] == snap:
            return
        self._undo_stack.append(snap)
        # Cap history to keep memory bounded.
        if len(self._undo_stack) > 200:
            self._undo_stack = self._undo_stack[-200:]
        # Any new edit invalidates the redo stack.
        self._redo_stack.clear()

    def _undo(self) -> None:
        # Need at least 2 entries: current + previous.
        if len(self._undo_stack) < 2:
            return
        self._suspend_history = True
        try:
            current = self._undo_stack.pop()
            self._redo_stack.append(current)
            prev = self._undo_stack[-1]
            self._restore_clips(prev)
            self._mark_dirty()
        finally:
            self._suspend_history = False

    def _redo(self) -> None:
        if not self._redo_stack:
            return
        self._suspend_history = True
        try:
            snap = self._redo_stack.pop()
            self._undo_stack.append(snap)
            self._restore_clips(snap)
            self._mark_dirty()
        finally:
            self._suspend_history = False

    # ---- waveform ----
    def _load_waveform_async(self) -> None:
        def _done(peaks, duration):
            # Apply waveform; only override stored duration if we got something useful.
            if duration > 0:
                self.tl.duration = duration
            self.canvas.set_data(self.tl.duration or duration or 60.0, peaks, self.canvas.clips)
            # On open, if this timeline already has clips, zoom out to fit the
            # entire song so users can immediately see the whole arrangement.
            if not self._did_initial_fit_zoom and self.canvas.clips:
                QTimer.singleShot(0, self._zoom_to_fit_song)
            self._update_time_label()
        _load_or_build_waveform(self.gui, self.item, _done)

    def _zoom_to_fit_song(self) -> None:
        """Set zoom so the full song duration fits in the visible viewport."""
        if self._did_initial_fit_zoom:
            return
        try:
            duration = max(1.0, float(self.canvas.duration or self.tl.duration or 60.0))
            vp_w = int(self.scroll.viewport().width()) if hasattr(self, 'scroll') else 0
            # If layout isn't ready yet, retry once shortly.
            if vp_w <= 80:
                QTimer.singleShot(40, self._zoom_to_fit_song)
                return
            # Leave a small margin so final second and handles remain visible.
            fit_width = max(120, vp_w - 40)
            pps = fit_width / duration
            self.canvas.set_zoom(pps)
            try:
                self.scroll.horizontalScrollBar().setValue(0)
            except Exception:
                pass
            self._did_initial_fit_zoom = True
        except Exception:
            pass

    # ---- transport / preview ----
    def _ensure_preview_player(self) -> None:
        if self._preview_player is not None:
            return
        if not self.item.video_path or not os.path.isfile(self.item.video_path):
            return
        try:
            from .visualizer_engine import _VideoAudioPlayer
        except ImportError:
            from visualizer_engine import _VideoAudioPlayer
        self._preview_player = _VideoAudioPlayer(
            self.item.video_path, loop=False)
        # Apply the same volume level used by the main visualizer engine,
        # including the per-song volume set on this item.
        try:
            if hasattr(self.gui, '_get_video_volume_multiplier'):
                vol = self.gui._get_video_volume_multiplier()
                # Also factor in the engine fader if available.
                eng = getattr(self.gui, '_viz_engine', None)
                fader = getattr(eng, '_fader_level', 1.0) if eng else 1.0
                item_vol = getattr(self.item, 'volume', 100) / 100.0
                self._preview_player.set_volume(max(0.0, min(1.0, fader * vol * item_vol)))
        except Exception:
            pass

    def _current_preview_position(self) -> float:
        """Return estimated playback position in seconds."""
        if not self._playing:
            return self._preview_position
        elapsed = time.monotonic() - self._preview_start_wall
        return self._preview_start_pos + elapsed

    def _toggle_play(self) -> None:
        if self._playing:
            self._pause_preview()
        else:
            self._start_preview()

    def _start_preview(self) -> None:
        # Timeline preview owns playback while active.
        _stop_external_playback_for_timeline(self.gui)

        # Pressing Play on the timeline should cancel any single-preset
        # preview so the timeline clips own the lights.
        self._stop_preset_preview()
        # Stop any existing player so we can seek to a new position
        if self._preview_player is not None:
            self._preview_player.release()
            self._preview_player = None
        self._ensure_preview_player()
        seek_pos = self.canvas.playhead
        if self._preview_player is not None:
            self._preview_player.play(start_seconds=seek_pos)
        self._preview_start_wall = time.monotonic()
        self._preview_start_pos = seek_pos
        self._playing = True
        self.btn_play.setText("⏸ Pause")
        self._ptimer.start()
        # Make sure the playhead is in view as we begin playing.
        self._follow_playhead()
        # Push video frames over NDI while the timeline is playing.
        self._start_ndi_video(seek_pos)

    def _pause_preview(self) -> None:
        # Record position, then kill the player (sounddevice can't actually pause)
        self._preview_position = self._current_preview_position()
        if self._preview_player is not None:
            self._preview_player.release()
            self._preview_player = None
        self._playing = False
        self.btn_play.setText("▶ Play")
        self._ptimer.stop()
        self._stop_all_preview_clips()
        self._stop_ndi_video()

    def _stop_preview(self) -> None:
        if self._preview_player is not None:
            self._preview_player.release()
            self._preview_player = None
        self._preview_position = 0.0
        self._playing = False
        self.btn_play.setText("▶ Play")
        self.canvas.playhead = 0.0
        self.canvas.update()
        self._update_time_label()
        self._stop_all_preview_clips()
        self._ptimer.stop()
        self._stop_ndi_video()
        # Snap view back to the start when stopped.
        try:
            bar = self.scroll.horizontalScrollBar()
            if bar is not None:
                bar.setValue(0)
        except Exception:
            pass

    def _rewind(self) -> None:
        was_playing = self._playing
        self._stop_preview()
        self.canvas.playhead = 0.0
        self.canvas.update()
        self._update_time_label()
        if was_playing:
            self._start_preview()

    def _stop_all_preview_clips(self) -> None:
        for c in list(self._preview_active_clips.values()):
            _stop_clip(self.gui, c, effect_id_prefix="stl_prev")
        self._preview_active_clips.clear()

    # ---- live preset preview (right-click → Preview) -------------------
    def _preview_eid(self, preset_id: str) -> str:
        return f"stl_preview_{preset_id}"

    def _on_preset_interaction(self) -> None:
        """Called when the user clicks a different preset row or starts a drag.

        If a preview is running and the user touches a *different* preset,
        cancel the preview per the UX spec.
        """
        if self._previewing_preset_id is None:
            return
        # If a row is selected, only cancel when it differs from the
        # currently-previewing preset (avoids cancelling on the row that
        # *is* being previewed).
        try:
            it = self.preset_list.currentItem()
            cur_pid = it.data(Qt.ItemDataRole.UserRole) if it is not None else None
        except Exception:
            cur_pid = None
        if cur_pid is None or cur_pid != self._previewing_preset_id:
            self._stop_preset_preview()

    def _start_preset_preview(self, preset_id: str, preset_name: str = "") -> None:
        if not preset_id:
            return
        # Always stop any prior preview first.
        self._stop_preset_preview()
        eid = self._preview_eid(preset_id)
        # Built-in Video Overlay presets bypass the effect engine: simulate
        # them via a synthetic clip whose length is reasonable for preview.
        if _is_builtin_overlay(preset_id):
            preview_len = 3.0
            # If a clip with this builtin id is currently selected, mirror
            # its length so a fade preview matches what the timeline will do.
            try:
                sel = self.canvas.selected_clip()
                if sel and sel.preset_id == preset_id and sel.length > 0:
                    preview_len = sel.length
            except Exception:
                pass
            # Build a synthetic clip for parameter lookup (SET %).
            fake = SongTimelineClip(
                id=f"prev_{preset_id}", preset_id=preset_id,
                preset_name=preset_name, start=0.0, length=preview_len,
            )
            if preset_id == _BUILTIN_OVERLAY_SET_PCT:
                try:
                    sel = self.canvas.selected_clip()
                    if sel and sel.preset_id == preset_id:
                        fake.params['overlay_pct'] = float(
                            sel.params.get('overlay_pct', 50.0))
                    else:
                        fake.params['overlay_pct'] = 50.0
                except Exception:
                    fake.params['overlay_pct'] = 50.0
            try:
                _fire_overlay_builtin(self.gui, fake, eid)
            except Exception as e:
                _stl_log(f"PREVIEW BUILTIN FAIL: {e}")
                return
            self._previewing_preset_id = preset_id
            try:
                self.lbl_hint.setText(
                    f"▶ Previewing: {preset_name or preset_id}  "
                    f"— click another preset or right-click → Stop to end.")
            except Exception:
                pass
            _stl_log(f"PREVIEW BUILTIN START: eid={eid}")
            return
        # Timeline fixture sequence preview: play it via the sequence player.
        if _is_sequence_preset(preset_id):
            fake = SongTimelineClip(
                id=f"prev_{preset_id}", preset_id=preset_id,
                preset_name=preset_name, start=0.0, length=4.0,
            )
            _fire_sequence(self.gui, fake)
            self._previewing_preset_id = preset_id
            try:
                self.lbl_hint.setText(
                    f"▶ Previewing: {preset_name or preset_id}  "
                    f"— click another preset or right-click → Stop to end.")
            except Exception:
                pass
            return
        eng = getattr(self.gui, 'effect_engine', None)
        if eng is None:
            return
        preset = _find_preset(self.gui, preset_id)
        if preset is None:
            _stl_log(f"PREVIEW SKIP (preset not found): id={preset_id}")
            return
        # Match timeline/live playback behavior for layered presets.
        layers_data = list(getattr(preset, 'layers', None) or [])
        if layers_data:
            try:
                from .models import EffectLayer
            except ImportError:
                from models import EffectLayer
            started: list = []
            for idx, ld in enumerate(layers_data):
                try:
                    layer = EffectLayer.from_dict(ld)
                    if not layer.enabled:
                        continue
                    lparams = layer.to_effect_params()
                    if (layer.layer_type == 'intensity'
                            and layer.effect_type == 'static'
                            and lparams.effect_type == 'pulse'):
                        lparams.effect_type = 'static'
                        lparams.intensity_min = layer.intensity
                        lparams.intensity_max = layer.intensity
                    layer_id = getattr(layer, 'id', '') or f"layer_{idx}"
                    layer_eid = f"{eid}__L{idx}_{layer_id}"
                    try:
                        eng.start_effect_htp(layer_eid, lparams,
                                             fade_in_time=0.0,
                                             fade_out_time=0.0,
                                             effect_duration=0.0)
                    except TypeError:
                        eng.start_effect_htp(layer_eid, lparams)
                    started.append(layer_eid)
                except Exception as e:
                    _stl_log(f"PREVIEW LAYER EXC idx={idx}: {e}")
            if not started:
                _stl_log(f"PREVIEW SKIP (no layer params): id={preset_id}")
                return
            self._preview_layer_eids = started
            self._previewing_preset_id = preset_id
            try:
                self.lbl_hint.setText(f"▶ Previewing: {preset_name or preset_id}  "
                                      f"— click another preset, drag, or right-click → Stop to end.")
            except Exception:
                pass
            _stl_log(f"PREVIEW START LAYERED: eid={eid} layers={len(started)}")
            return
        params = _build_effect_params(preset)
        if params is None:
            _stl_log(f"PREVIEW SKIP (no params): id={preset_id}")
            return
        try:
            # Infinite duration: 0.0 → run until explicitly stopped.
            eng.start_effect_htp(eid, params,
                                 fade_in_time=0.0,
                                 fade_out_time=0.0,
                                 effect_duration=0.0)
        except TypeError:
            eng.start_effect_htp(eid, params)
        except Exception as e:
            _stl_log(f"PREVIEW START FAIL: {e}")
            return
        self._preview_layer_eids = []
        self._previewing_preset_id = preset_id
        try:
            self.lbl_hint.setText(f"▶ Previewing: {preset_name or preset_id}  "
                                  f"— click another preset, drag, or right-click → Stop to end.")
        except Exception:
            pass
        _stl_log(f"PREVIEW START: eid={eid}")

    def _stop_preset_preview(self) -> None:
        pid = self._previewing_preset_id
        if not pid:
            return
        self._previewing_preset_id = None
        eid = self._preview_eid(pid)
        if _is_builtin_overlay(pid):
            try:
                _cancel_overlay_active(eid)
            except Exception as e:
                _stl_log(f"PREVIEW BUILTIN STOP FAIL: {e}")
        elif _is_sequence_preset(pid):
            seq_id = pid.split(":", 1)[1]
            try:
                self.gui._stop_fixture_sequence(seq_id, restore=True)
            except Exception as e:
                _stl_log(f"PREVIEW SEQ STOP FAIL: {e}")
        else:
            eng = getattr(self.gui, 'effect_engine', None)
            if eng is not None:
                layer_eids = list(self._preview_layer_eids or [])
                self._preview_layer_eids = []
                if layer_eids:
                    for leid in layer_eids:
                        try:
                            eng.stop_effect_htp(leid)
                        except Exception as e:
                            _stl_log(f"PREVIEW STOP LAYER FAIL {leid[:30]}: {e}")
                else:
                    try:
                        eng.stop_effect_htp(eid)
                    except Exception as e:
                        _stl_log(f"PREVIEW STOP FAIL: {e}")
        try:
            self.lbl_hint.setText(
                "Drag preset onto lane • Drag clip / handles to move/resize • "
                "Ctrl/Shift+click for multi-select • Ctrl+C/V/X/D • Ctrl+Z/Y undo • "
                "Right-click preset → Preview"
            )
        except Exception:
            pass
        _stl_log(f"PREVIEW STOP: id={pid}")

    # ---- NDI video pass-through during timeline play -------------------
    def _start_ndi_video(self, seek_pos: float = 0.0) -> None:
        """Play this song's video through the main visualizer engine (with
        audio muted) so it appears on the NDI output while the timeline
        editor drives audio + lighting.
        """
        if self._ndi_video_active:
            return
        item = self.item
        if not item or getattr(item, 'source_type', '') != 'video':
            return
        if not getattr(item, 'video_path', ''):
            return
        eng = getattr(self.gui, '_viz_engine', None) or getattr(self.gui, 'viz_engine', None)
        if eng is None:
            return
        # Only push to NDI if NDI is currently active on the main engine —
        # we don't auto-start NDI here to avoid surprising the user.
        try:
            ndi_active = bool(getattr(eng, '_ndi_sender', None) and
                              eng._ndi_sender.is_active)
        except Exception:
            ndi_active = False
        if not ndi_active:
            _stl_log("NDI VIDEO SKIP: NDI sender not active")
            return
        try:
            eng.play(item)
        except Exception as e:
            _stl_log(f"NDI VIDEO play() failed: {e}")
            return
        # Mute the engine's audio so we don't double-up with the editor's
        # sounddevice playback. Save prior volume to restore on stop.
        try:
            ap = getattr(eng, '_audio_player', None)
            if ap is not None:
                self._viz_audio_muted_prev = getattr(ap, '_volume', 1.0)
                ap.set_volume(0.0)
        except Exception:
            pass
        # Seek the engine's audio (even though muted) so any internal
        # timing aligns with the editor playhead.
        try:
            ap = getattr(eng, '_audio_player', None)
            if ap is not None and hasattr(ap, 'seek'):
                ap.seek(seek_pos)
        except Exception:
            pass
        self._ndi_video_active = True
        _stl_log(f"NDI VIDEO START at {seek_pos:.2f}s")

    def _stop_ndi_video(self) -> None:
        if not self._ndi_video_active:
            return
        self._ndi_video_active = False
        eng = getattr(self.gui, '_viz_engine', None) or getattr(self.gui, 'viz_engine', None)
        if eng is None:
            return
        try:
            eng.stop()
        except Exception as e:
            _stl_log(f"NDI VIDEO stop() failed: {e}")
        # Restore prior audio volume if we changed it.
        try:
            if self._viz_audio_muted_prev is not None:
                ap = getattr(eng, '_audio_player', None)
                if ap is not None:
                    ap.set_volume(self._viz_audio_muted_prev)
                self._viz_audio_muted_prev = None
        except Exception:
            pass
        _stl_log("NDI VIDEO STOP")

    def _tick_preview(self) -> None:
        # Wrap the whole tick in a try/except: a single exception here would
        # otherwise kill the timer and freeze the UI as users perceive it.
        try:
            # Skip ticks while the user is performing a drag-and-drop on this
            # dialog — calling effect_engine code from inside Qt's nested DnD
            # event loop can re-enter Qt and lock the main thread.
            from PyQt6.QtWidgets import QApplication
            if QApplication.mouseButtons() & Qt.MouseButton.LeftButton and self.canvas._drag_mode is None:
                # mouse held outside our own canvas drag handling → likely DnD
                pass  # still update playhead, but don't fire clips below

            # Drive playhead from wall-clock time (sounddevice player has no position API)
            if self._playing:
                self.canvas.playhead = min(
                    self.canvas.duration,
                    self._current_preview_position()
                )
                # Auto-stop when we reach the end
                if self.canvas.playhead >= self.canvas.duration:
                    self._stop_preview()
                    return
            t = self.canvas.playhead

            # Build a small worklist of (clip, action) and dispatch via
            # singleShot so effect-engine work runs *outside* the timer
            # callback / any nested event loop.
            to_fire: list = []
            to_stop: list = []
            for c in self.canvas.clips:
                cid = c.id
                if not self.canvas.is_clip_audible(c):
                    if cid in self._preview_active_clips:
                        self._preview_active_clips.pop(cid, None)
                        to_stop.append(c)
                    continue
                is_trigger = getattr(c, 'clip_type', 'preset') == 'trigger'
                if is_trigger:
                    # Fire once per preview session when playhead crosses start.
                    if t >= c.start and cid not in self._preview_active_clips:
                        self._preview_active_clips[cid] = c
                        to_fire.append(c)
                    continue
                in_win = c.start <= t < (c.start + c.length)
                if in_win and cid not in self._preview_active_clips:
                    _stl_log(f"TICK ENTER window: clip={cid[:8]} t={t:.2f} start={c.start:.2f} end={c.start+c.length:.2f}")
                    self._preview_active_clips[cid] = c
                    to_fire.append(c)
                elif not in_win and cid in self._preview_active_clips:
                    _stl_log(f"TICK EXIT window: clip={cid[:8]} t={t:.2f} start={c.start:.2f} end={c.start+c.length:.2f}")
                    self._preview_active_clips.pop(cid, None)
                    to_stop.append(c)

            if to_fire or to_stop:
                gui = self.gui
                def _dispatch(fire=to_fire, stop=to_stop, g=gui):
                    for c in stop:
                        try:
                            _stop_clip(g, c, effect_id_prefix="stl_prev")
                        except Exception as e:
                            print(f"[SongTimeline] preview _stop_clip failed: {e}")
                    for c in fire:
                        try:
                            _fire_clip(g, c, effect_id_prefix="stl_prev")
                        except Exception as e:
                            print(f"[SongTimeline] preview _fire_clip failed: {e}")
                QTimer.singleShot(0, _dispatch)

            # Repaint only the playhead+ruler area, not the whole widget.
            self.canvas.update()
            self._update_time_label()
            # Keep the playhead visible by auto-scrolling the viewport.
            self._follow_playhead()
            # Auto-stop at end
            if self.canvas.duration > 0 and self.canvas.playhead >= self.canvas.duration - 0.01:
                self._stop_preview()
        except Exception as e:
            print(f"[SongTimeline] _tick_preview exception: {e}")
            import traceback; traceback.print_exc()

    def _update_time_label(self) -> None:
        def fmt(t):
            m = int(t) // 60
            s = t - m * 60
            return f"{m}:{s:04.1f}"
        self.lbl_time.setText(f"{fmt(self.canvas.playhead)} / {fmt(self.canvas.duration)}")

    def _follow_playhead(self) -> None:
        """Scroll the timeline viewport so the playhead stays in view.

        Pages forward when the playhead enters the right ~25% of the
        visible area; pages backward if it has drifted left of view
        (e.g. after a rewind/seek).
        """
        scroll = getattr(self, 'scroll', None)
        canvas = getattr(self, 'canvas', None)
        if scroll is None or canvas is None:
            return
        try:
            bar = scroll.horizontalScrollBar()
            if bar is None or not bar.isVisible():
                return
            vp_w = scroll.viewport().width()
            if vp_w <= 0:
                return
            playhead_x = int(canvas.time_to_x(canvas.playhead))
            cur = bar.value()
            # If playhead is past 75% of the viewport, jump it back to 25%.
            right_threshold = cur + int(vp_w * 0.75)
            left_threshold = cur + int(vp_w * 0.05)
            if playhead_x >= right_threshold:
                target = max(0, playhead_x - int(vp_w * 0.25))
                bar.setValue(min(bar.maximum(), target))
            elif playhead_x < left_threshold:
                target = max(0, playhead_x - int(vp_w * 0.10))
                bar.setValue(min(bar.maximum(), target))
        except Exception:
            # Auto-scroll is a nicety — never let it break playback.
            pass

    def _build_preset_target_map(self) -> dict:
        """Return lightweight target metadata keyed by preset_id.

        Used only for overlap conflict tinting in the editor.
        """
        out = {}
        for p in (getattr(getattr(self.gui, 'project', None), 'presets', []) or []):
            groups = {str(g).strip().lower() for g in (getattr(p, 'target_groups', []) or []) if str(g).strip()}
            fixtures = {str(f).strip() for f in (getattr(p, 'target_fixtures', []) or []) if str(f).strip()}
            out[p.id] = {
                'groups': groups,
                'fixtures': fixtures,
                'all': ('all' in groups),
            }
        return out

    def _set_lane_state(self, lane: int, key: str, value: bool) -> None:
        self.canvas.set_lane_state(lane, key, value)
        self._refresh_lane_controls()

    def _refresh_lane_controls(self) -> None:
        lane_count = self.canvas.lane_count()
        base_style = (
            "QPushButton {"
            "  padding: 3px 8px;"
            "  font-size: 11px;"
            "  font-weight: 600;"
            "  color: #d6d6d6;"
            "  background: #2b2b2b;"
            "  border: 1px solid #4a4a4a;"
            "  border-radius: 4px;"
            "}"
        )
        for i, ctrls in enumerate(getattr(self, '_lane_controls', [])):
            wrap, btn_m, btn_s, btn_l = ctrls
            visible = i < lane_count
            wrap.setVisible(visible)
            st = self.canvas.get_lane_state(i)
            for btn, key, on_col in (
                (btn_m, 'mute', '#b45309'),
                (btn_s, 'solo', '#166534'),
                (btn_l, 'lock', '#1d4ed8'),
            ):
                btn.blockSignals(True)
                btn.setChecked(bool(st.get(key, False)))
                btn.blockSignals(False)
                if st.get(key, False):
                    btn.setStyleSheet(
                        "QPushButton {"
                        "  padding: 3px 8px;"
                        "  font-size: 11px;"
                        "  font-weight: 700;"
                        f"  background:{on_col};"
                        "  color:white;"
                        "  border:1px solid #4a4a4a;"
                        "  border-radius: 4px;"
                        "}"
                    )
                else:
                    btn.setStyleSheet(base_style)

    # ---- inspector ----
    def _on_selection(self, clip) -> None:
        if clip is None:
            self._set_inspector_enabled(False)
            self._refresh_lane_controls()
            return
        is_trigger = getattr(clip, 'clip_type', 'preset') == 'trigger'
        self._set_inspector_enabled(True, is_trigger=is_trigger)
        self.sp_start.blockSignals(True); self.sp_start.setValue(clip.start); self.sp_start.blockSignals(False)
        if not is_trigger:
            for sp, v in ((self.sp_len, clip.length),
                          (self.sp_fin, clip.fade_in),
                          (self.sp_fout, clip.fade_out)):
                sp.blockSignals(True); sp.setValue(v); sp.blockSignals(False)
        # Overlay-% inspector: visible only for the "SET %" builtin (and never for triggers).
        is_set_pct = (clip.preset_id == _BUILTIN_OVERLAY_SET_PCT) and not is_trigger
        try:
            self.lbl_overlay_pct.setVisible(is_set_pct)
            self.sp_overlay_pct.setVisible(is_set_pct)
        except Exception:
            pass
        if is_set_pct:
            try:
                pct = float(clip.params.get('overlay_pct', 50.0))
            except Exception:
                pct = 50.0
            self.sp_overlay_pct.blockSignals(True)
            self.sp_overlay_pct.setValue(pct)
            self.sp_overlay_pct.blockSignals(False)
        self._refresh_lane_controls()

    def _set_inspector_enabled(self, on: bool, *, is_trigger: bool = False) -> None:
        self.sp_start.setEnabled(on)
        self.btn_del.setEnabled(on)
        # Length and fade controls are not applicable for one-shot triggers.
        for w in (self.sp_len, self.sp_fin, self.sp_fout):
            w.setEnabled(on and not is_trigger)
            w.setVisible(not is_trigger if on else True)
        self.sp_overlay_pct.setEnabled(on and not is_trigger)

    def _inspector_apply(self) -> None:
        c = self.canvas.selected_clip()
        if not c:
            return
        c.start = max(0.0, min(self.canvas.duration - 0.05, self.sp_start.value()))
        is_trigger = getattr(c, 'clip_type', 'preset') == 'trigger'
        if not is_trigger:
            c.length = max(0.05, min(self.canvas.duration - c.start, self.sp_len.value()))
            c.fade_in = self.sp_fin.value()
            c.fade_out = self.sp_fout.value()
        if c.preset_id == _BUILTIN_OVERLAY_SET_PCT and not is_trigger:
            c.params['overlay_pct'] = float(self.sp_overlay_pct.value())
        self.canvas._refresh_conflict_cache()
        self.canvas.update()
        self._mark_dirty()

    # ---- trim changed ----
    def _on_trim_changed(self, ts: float, te: float) -> None:
        """Called when the user drags a trim handle on the waveform."""
        self.item.trim_start = ts
        self.item.trim_end = te
        # Keep spinboxes in sync without re-triggering the signal
        self.sp_trim_start.blockSignals(True)
        self.sp_trim_start.setValue(ts)
        self.sp_trim_start.blockSignals(False)
        self.sp_trim_end.blockSignals(True)
        self.sp_trim_end.setValue(te)
        self.sp_trim_end.blockSignals(False)
        self._mark_dirty()

    def _on_trim_spinbox_changed(self) -> None:
        """Called when the user edits the trim spinboxes directly."""
        ts = self.sp_trim_start.value()
        te = self.sp_trim_end.value()
        # Clamp: start < end (if end != 0)
        if te > 0 and ts >= te:
            ts = max(0.0, te - 0.1)
            self.sp_trim_start.blockSignals(True)
            self.sp_trim_start.setValue(ts)
            self.sp_trim_start.blockSignals(False)
        self.canvas.trim_start = ts
        self.canvas.trim_end = te
        self.canvas.update()
        self.item.trim_start = ts
        self.item.trim_end = te
        self._mark_dirty()

    def _reset_trim(self) -> None:
        """Reset both trim handles to default (full song)."""
        self.sp_trim_start.blockSignals(True); self.sp_trim_start.setValue(0.0); self.sp_trim_start.blockSignals(False)
        self.sp_trim_end.blockSignals(True); self.sp_trim_end.setValue(0.0); self.sp_trim_end.blockSignals(False)
        self.canvas.trim_start = 0.0
        self.canvas.trim_end = 0.0
        self.canvas.update()
        self.item.trim_start = 0.0
        self.item.trim_end = 0.0
        self._mark_dirty()

    def _on_volume_spinbox_changed(self) -> None:
        """Called when the user changes the per-song volume spinbox."""
        self.item.volume = self.sp_volume.value()
        self._mark_dirty()

    # ---- canvas changed ----
    def _on_canvas_changed(self) -> None:
        # keep inspector in sync if currently selected
        c = self.canvas.selected_clip()
        if c is not None:
            is_trigger = getattr(c, 'clip_type', 'preset') == 'trigger'
            self.sp_start.blockSignals(True); self.sp_start.setValue(c.start); self.sp_start.blockSignals(False)
            if not is_trigger:
                for sp, v in ((self.sp_len, c.length),
                              (self.sp_fin, c.fade_in),
                              (self.sp_fout, c.fade_out)):
                    sp.blockSignals(True); sp.setValue(v); sp.blockSignals(False)
            # Toggle overlay-% widget visibility on canvas-driven changes
            # (e.g. selection switching to a different clip via canvas).
            is_set_pct = (c.preset_id == _BUILTIN_OVERLAY_SET_PCT) and not is_trigger
            try:
                self.lbl_overlay_pct.setVisible(is_set_pct)
                self.sp_overlay_pct.setVisible(is_set_pct)
                if is_set_pct:
                    pct = float(c.params.get('overlay_pct', 50.0))
                    self.sp_overlay_pct.blockSignals(True)
                    self.sp_overlay_pct.setValue(pct)
                    self.sp_overlay_pct.blockSignals(False)
            except Exception:
                pass
        self.canvas._refresh_conflict_cache()
        self._push_history()
        self._refresh_lane_controls()
        self._mark_dirty()

    def _mark_dirty(self) -> None:
        self._dirty = True
        if not self.windowTitle().endswith(" *"):
            self.setWindowTitle(self.windowTitle() + " *")

    # ---- zoom ----
    def _zoom(self, factor: float) -> None:
        self.canvas.set_zoom(self.canvas.pixels_per_sec * factor)

    # ---- save/close ----
    def _save(self) -> None:
        self.tl.clips = list(self.canvas.clips)
        if self.canvas.duration:
            self.tl.duration = self.canvas.duration
        # Persist trim points back to the VisualizerItem so playback respects them.
        self.item.trim_start = self.canvas.trim_start
        self.item.trim_end = self.canvas.trim_end
        save_timeline(self.gui, self.item, self.tl)
        self._dirty = False
        t = self.windowTitle()
        if t.endswith(" *"):
            self.setWindowTitle(t[:-2])

    def _save_and_close(self) -> None:
        self._save()
        self.accept()

    def _confirm_discard_unsaved(self) -> Optional[bool]:
        """If there are unsaved changes, ask the user what to do.

        Returns:
            True  → caller should proceed with closing (changes either
                    saved or explicitly discarded).
            False → caller should cancel the close.
            None  → no prompt was needed (nothing to save).
        """
        if not self._dirty:
            return None
        # Guard against re-entrant prompts (e.g. closeEvent → done()).
        if getattr(self, '_close_prompt_active', False):
            return True
        self._close_prompt_active = True
        try:
            box = QMessageBox(self)
            box.setIcon(QMessageBox.Icon.Question)
            box.setWindowTitle("Unsaved changes")
            box.setText(f"Save changes to the timeline for "
                        f"\"{getattr(self.item, 'name', 'this song')}\" "
                        f"before closing?")
            save_btn = box.addButton("Save", QMessageBox.ButtonRole.AcceptRole)
            discard_btn = box.addButton("Discard", QMessageBox.ButtonRole.DestructiveRole)
            cancel_btn = box.addButton("Cancel", QMessageBox.ButtonRole.RejectRole)
            box.setDefaultButton(save_btn)
            box.exec()
            clicked = box.clickedButton()
            if clicked is cancel_btn:
                return False
            if clicked is save_btn:
                try:
                    self._save()
                except Exception as e:
                    QMessageBox.warning(self, "Save failed",
                                        f"Could not save timeline:\n{e}")
                    return False
                return True
            # Discard: mark clean so the auto-save in done()/closeEvent
            # won't re-persist the unwanted changes.
            self._dirty = False
            return True
        finally:
            self._close_prompt_active = False

    def _shutdown_playback(self) -> None:
        """Tear down anything that could still emit audio/video after the
        dialog goes away. Safe to call multiple times."""
        for fn in (self._stop_preview, self._stop_preset_preview,
                   self._stop_ndi_video):
            try:
                fn()
            except Exception:
                pass
        # Final hard-stop on the audio player in case _stop_preview was
        # short-circuited by an exception earlier.
        try:
            if self._preview_player is not None:
                self._preview_player.release()
                self._preview_player = None
        except Exception:
            pass
        try:
            if self._ptimer.isActive():
                self._ptimer.stop()
        except Exception:
            pass

    def done(self, result):
        # Called by both accept() and reject(); ensures audio/video stop
        # even when the user uses the Save & Close button (which doesn't
        # always fire closeEvent on a modeless dialog).
        # Save & Close has already saved; for any other close path (Esc,
        # reject, etc.) prompt if there are unsaved changes.
        if result != QDialog.DialogCode.Accepted:
            decision = self._confirm_discard_unsaved()
            if decision is False:
                # User chose Cancel — abort the close.
                return
        self._shutdown_playback()
        super().done(result)

    def closeEvent(self, ev):
        # X / system close: prompt before discarding.
        decision = self._confirm_discard_unsaved()
        if decision is False:
            ev.ignore()
            return
        self._shutdown_playback()
        super().closeEvent(ev)


# ---------------------------------------------------------------------------
#  Public entry point — opens the editor
# ---------------------------------------------------------------------------

def open_timeline_editor(gui, item) -> None:
    if not item.video_path:
        QMessageBox.information(
            gui, "Edit Timeline",
            "This item has no media file, so a song timeline cannot be created.")
        return
    try:
        # Opening timeline editing should stop any unrelated playback first.
        _stop_external_playback_for_timeline(gui)
        dlg = SongTimelineEditor(gui, item, parent=gui)
        dlg.exec()
    except Exception as _e:
        import traceback as _tb
        _tb.print_exc()
        QMessageBox.critical(gui, "Timeline Error",
                             f"Failed to open timeline editor:\n{_e}")
