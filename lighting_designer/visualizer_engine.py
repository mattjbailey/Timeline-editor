"""

Visualizer Engine — manages playback of video files and generated effects,

spatial DMX mapping to fixtures, and fullscreen output to a second monitor.

"""



from __future__ import annotations



import math

import os

import time

import threading

import uuid

from dataclasses import dataclass, field

from typing import Optional, TYPE_CHECKING





# ---------------------------------------------------------------------------

#  File-based diagnostic logger (survives --noconsole builds)

# ---------------------------------------------------------------------------



_VIZ_LOG_PATH = os.path.join(os.path.expanduser("~"), "viz_debug.log")

# Optional error reporter — set by main.py after Appertini is initialised.
# Signature: _error_reporter(exc_type, exc_value, exc_tb, *, context: str) -> None
_error_reporter = None


def _viz_report_error(exc: Exception, context: str) -> None:
    """Report *exc* to Appertini (if the reporter hook is registered) and log it."""
    _viz_log(f"[VizEngine] Error ({context}): {exc}")
    if _error_reporter is not None:
        try:
            import sys as _sys
            _error_reporter(
                type(exc), exc, exc.__traceback__,
                context=context,
            )
        except Exception:
            pass



def _viz_log(msg: str):

    """Write a timestamped diagnostic line to ~/viz_debug.log AND stdout."""

    line = f"[{time.strftime('%H:%M:%S')}] {msg}"

    try:

        print(line, flush=True)

    except Exception:

        pass

    try:

        with open(_VIZ_LOG_PATH, "a", encoding="utf-8") as f:

            f.write(line + "\n")

    except Exception:

        pass



from PyQt6.QtWidgets import (

    QWidget, QLabel, QVBoxLayout, QHBoxLayout, QComboBox, QPushButton,

    QApplication, QSizePolicy,

)

from PyQt6.QtCore import Qt, QTimer, QSize, pyqtSignal, QObject, QRectF, QUrl

from PyQt6.QtGui import QImage, QPainter, QColor, QPixmap


# ---------------------------------------------------------------------------
#  GPU-accelerated rendering support (optional — CPU fallback if unavailable)
# ---------------------------------------------------------------------------
_HAS_OPENGL = False
try:
    from PyQt6.QtOpenGL import (
        QOpenGLFramebufferObject,
        QOpenGLFramebufferObjectFormat,
        QOpenGLPaintDevice,
    )
    from PyQt6.QtGui import QOpenGLContext, QOffscreenSurface, QSurfaceFormat
    _HAS_OPENGL = True
except ImportError:
    pass



# Audio playback for video overlay (lazy — only imported when needed)

_QMediaPlayer = None

_QAudioOutput = None

def _ensure_audio_imports():

    global _QMediaPlayer, _QAudioOutput

    if _QMediaPlayer is None:

        try:

            from PyQt6.QtMultimedia import QMediaPlayer, QAudioOutput

            _QMediaPlayer = QMediaPlayer

            _QAudioOutput = QAudioOutput

        except ImportError:

            pass



try:

    from .visualizer_effects import (

        BaseVisualEffect, VisualEffectParams,

        VISUAL_EFFECT_REGISTRY, create_effect, get_effect_names,

    )

except ImportError:

    from visualizer_effects import (

        BaseVisualEffect, VisualEffectParams,

        VISUAL_EFFECT_REGISTRY, create_effect, get_effect_names,

    )



if TYPE_CHECKING:

    try:

        from .artnet import ArtNetOutput

        from .models import PatchedFixture, LightingProject

    except ImportError:

        from artnet import ArtNetOutput

        from models import PatchedFixture, LightingProject


# ---------------------------------------------------------------------------
#  GPU offscreen renderer — QPainter ➜ OpenGL FBO ➜ QImage
# ---------------------------------------------------------------------------

class _GPUOffscreenRenderer:
    """Manages an offscreen OpenGL context + FBO for GPU-accelerated QPainter.

    All 47 visual effects draw via QPainter.  When the paint device is an
    OpenGL surface the Qt render back-end routes every draw call through the
    GPU, giving us hardware-accelerated anti-aliasing, compositing and
    blending essentially for free.

    Usage::

        gpu = _GPUOffscreenRenderer()
        if gpu.available:
            img = gpu.render(effect, w, h, t, params)
        else:
            ...  # fall back to CPU QImage path
    """

    def __init__(self) -> None:
        self.available: bool = False
        self._ctx: QOpenGLContext | None = None
        self._surface: QOffscreenSurface | None = None
        self._fbo: QOpenGLFramebufferObject | None = None
        self._device: QOpenGLPaintDevice | None = None
        self._fbo_w: int = 0
        self._fbo_h: int = 0

        if not _HAS_OPENGL:
            return
        try:
            self._surface = QOffscreenSurface()
            fmt = QSurfaceFormat()
            fmt.setMajorVersion(2)
            fmt.setMinorVersion(0)
            fmt.setProfile(QSurfaceFormat.OpenGLContextProfile.CompatibilityProfile)
            self._surface.setFormat(fmt)
            self._surface.create()
            if not self._surface.isValid():
                _viz_log("[GPU] offscreen surface invalid")
                return

            self._ctx = QOpenGLContext()
            self._ctx.setFormat(self._surface.format())
            if not self._ctx.create():
                _viz_log("[GPU] OpenGL context creation failed")
                return

            self.available = True
            _viz_log("[GPU] offscreen renderer initialised OK")
        except Exception as exc:
            _viz_log(f"[GPU] init failed: {exc}")
            self.available = False

    # ------------------------------------------------------------------

    def _ensure_fbo(self, w: int, h: int) -> bool:
        """Create / resize the FBO to match the requested dimensions."""
        if self._fbo is not None and self._fbo_w == w and self._fbo_h == h:
            return True
        try:
            self._ctx.makeCurrent(self._surface)
            fmt = QOpenGLFramebufferObjectFormat()
            # No multisampling — keeps toImage() fast and avoids
            # blit-resolve overhead.  QPainter antialiasing still works.
            self._fbo = QOpenGLFramebufferObject(w, h, fmt)
            self._device = QOpenGLPaintDevice(w, h)
            self._fbo_w = w
            self._fbo_h = h
            self._ctx.doneCurrent()
            return True
        except Exception as exc:
            _viz_log(f"[GPU] FBO resize failed: {exc}")
            self._fbo = None
            self._device = None
            return False

    # ------------------------------------------------------------------

    def render(
        self,
        effect: BaseVisualEffect,
        w: int,
        h: int,
        t: float,
        params: VisualEffectParams,
    ) -> QImage | None:
        """Render *effect* on the GPU and return a QImage (ARGB32).

        Returns ``None`` on failure so the caller can fall back to CPU.
        """
        if not self.available:
            return None
        if not self._ensure_fbo(w, h):
            return None
        try:
            self._ctx.makeCurrent(self._surface)
            self._fbo.bind()

            painter = QPainter()
            if not painter.begin(self._device):
                self._fbo.release()
                self._ctx.doneCurrent()
                return None

            # Clear to black
            painter.setCompositionMode(
                QPainter.CompositionMode.CompositionMode_Source
            )
            painter.fillRect(0, 0, w, h, QColor(0, 0, 0))
            painter.setCompositionMode(
                QPainter.CompositionMode.CompositionMode_SourceOver
            )
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)

            # Apply global zoom transform
            zoom = getattr(params, 'scale', 1.0)
            if zoom != 1.0:
                cx, cy = w / 2.0, h / 2.0
                painter.translate(cx, cy)
                painter.scale(zoom, zoom)
                painter.translate(-cx, -cy)

            # --- actually draw the effect ---
            effect.render(painter, w, h, t, params)

            painter.end()

            result = self._fbo.toImage()  # GPU ➜ CPU read-back
            self._fbo.release()
            self._ctx.doneCurrent()
            return result
        except Exception as exc:
            _viz_log(f"[GPU] render failed: {exc}")
            try:
                self._ctx.doneCurrent()
            except Exception:
                pass
            return None

    # ------------------------------------------------------------------

    def destroy(self) -> None:
        """Release GPU resources."""
        try:
            if self._ctx and self._surface:
                self._ctx.makeCurrent(self._surface)
                self._fbo = None
                self._device = None
                self._ctx.doneCurrent()
            self._ctx = None
            self._surface = None
            self.available = False
        except Exception:
            pass


# ---------------------------------------------------------------------------

#  Data model for Visualizer items (buttons / pages)

# ---------------------------------------------------------------------------



@dataclass

class VisualizerItem:

    """One assignable button — either a video file or a generated effect."""

    id: str = ""

    name: str = "Untitled"

    color: str = "#c97a50"

    # Source type

    source_type: str = "effect"    # "effect" or "video"

    # Video fields

    video_path: str = ""

    proxy_path: str = ""  # transcoded MJPEG proxy for fast decode

    source_url: str = ""  # original URL (YouTube, etc.) for re-download / display

    loop: bool = True

    # Effect fields

    effect_type: str = "gradient_sweep"

    effect_params: Optional[VisualEffectParams] = None

    # MIDI

    midi_channel: int = -1

    midi_note: int = -1

    midi_cc: int = -1

    # Per-item audio trim (seconds).  trim_start: skip this many seconds at the
    # beginning.  trim_end: stop at this position (0.0 = natural end of file).
    trim_start: float = 0.0
    trim_end: float = 0.0

    # Per-item volume (0-100). Applied on top of the global video volume slider.
    volume: int = 100

    # Persisted thumbnail (base64 PNG)

    custom_thumbnail_b64: str = ""



    def __post_init__(self):

        if not self.id:

            self.id = str(uuid.uuid4())

        if self.effect_params is None:

            self.effect_params = VisualEffectParams()



    def to_dict(self) -> dict:

        d = {

            'id': self.id,

            'name': self.name,

            'color': self.color,

            'source_type': self.source_type,

            'video_path': self.video_path,

            'proxy_path': self.proxy_path,

            'source_url': self.source_url,

            'loop': self.loop,

            'effect_type': self.effect_type,

            'effect_params': self.effect_params.to_dict() if self.effect_params else {},

            'midi_channel': self.midi_channel,

            'midi_note': self.midi_note,

            'midi_cc': self.midi_cc,

        }

        if self.trim_start:
            d['trim_start'] = self.trim_start
        if self.trim_end:
            d['trim_end'] = self.trim_end
        if self.volume != 100:
            d['volume'] = self.volume
        if self.custom_thumbnail_b64:

            d['custom_thumbnail_b64'] = self.custom_thumbnail_b64

        return d



    @classmethod

    def from_dict(cls, data: dict) -> 'VisualizerItem':

        params = VisualEffectParams.from_dict(data.get('effect_params', {}))

        # Migrate legacy fixture_* keys to fixture_aware_*
        etype = data.get('effect_type', 'gradient_sweep')
        if etype and etype.startswith("fixture_") and not etype.startswith("fixture_aware_"):
            etype = etype.replace("fixture_", "fixture_aware_", 1)

        return cls(

            id=data.get('id', str(uuid.uuid4())),

            name=data.get('name', 'Untitled'),

            color=data.get('color', '#c97a50'),

            source_type=data.get('source_type', 'effect'),

            video_path=data.get('video_path', ''),

            proxy_path=data.get('proxy_path', ''),

            source_url=data.get('source_url', ''),

            loop=data.get('loop', True),

            effect_type=etype,

            effect_params=params,

            midi_channel=data.get('midi_channel', -1),

            midi_note=data.get('midi_note', -1),

            midi_cc=data.get('midi_cc', -1),

            custom_thumbnail_b64=data.get('custom_thumbnail_b64', ''),

            trim_start=float(data.get('trim_start', 0.0)),
            trim_end=float(data.get('trim_end', 0.0)),
            volume=int(data.get('volume', 100)),
        )





@dataclass

class VisualizerPage:

    """One page of visualizer buttons."""

    id: str = ""

    name: str = "Page 1"

    item_ids: list[str] = field(default_factory=list)



    def __post_init__(self):

        if not self.id:

            self.id = str(uuid.uuid4())



    def to_dict(self) -> dict:

        return {

            'id': self.id,

            'name': self.name,

            'item_ids': list(self.item_ids),

        }



    @classmethod

    def from_dict(cls, data: dict) -> 'VisualizerPage':

        return cls(

            id=data.get('id', str(uuid.uuid4())),

            name=data.get('name', 'Page 1'),

            item_ids=data.get('item_ids', []),

        )





# ---------------------------------------------------------------------------

#  Preview / Render widget

# ---------------------------------------------------------------------------


class VisualizerCanvas(QWidget):

    """Widget that displays the current visualizer frame (preview or fullscreen)."""



    def __init__(self, parent=None):

        super().__init__(parent)

        self._frame: QImage | None = None

        self._status_text: str = ""  # overlay status text

        self._frame_count: int = 0

        self.setMinimumSize(160, 90)

        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)

        self.setStyleSheet("background-color: #000000;")

        self.setAttribute(Qt.WidgetAttribute.WA_OpaquePaintEvent, True)



    def resizeEvent(self, event):

        super().resizeEvent(event)

        self.update()  # repaint with new size



    def set_frame(self, frame: QImage):

        self._frame = frame

        self._frame_count += 1

        self.update()  # schedule async repaint — avoids blocking the render timer



    def set_status(self, text: str):

        """Show a status message on the canvas (e.g. 'Loading...', error text)."""

        self._status_text = text

        self.update()  # async repaint — avoids blocking the caller



    def clear_status(self):

        self._status_text = ""



    def paintEvent(self, event):

        painter = QPainter(self)

        # Always clear to black first so stale pixels from a previous
        # frame (e.g. different aspect ratio) never bleed through.
        painter.fillRect(self.rect(), QColor(0, 0, 0))

        if self._frame and not self._frame.isNull():

            fw = self._frame.width()
            fh = self._frame.height()
            tw = self.width()
            th = self.height()

            if fw == tw and fh == th:
                # Fast path: frame matches widget exactly — no scaling
                painter.drawImage(0, 0, self._frame)
            else:
                # Scale to fit widget while maintaining aspect ratio
                src_ratio = fw / max(fh, 1)
                tgt_ratio = tw / max(th, 1)
                if src_ratio > tgt_ratio:
                    w = tw
                    h = int(w / src_ratio)
                    x = 0
                    y = (th - h) // 2
                else:
                    h = th
                    w = int(h * src_ratio)
                    x = (tw - w) // 2
                    y = 0
                painter.drawImage(QRectF(x, y, w, h), self._frame)

        else:

            painter.fillRect(self.rect(), QColor(0, 0, 0))

            if self._status_text:

                painter.setPen(QColor(200, 120, 80))  # amber

                font = painter.font()

                font.setPointSize(12)

                painter.setFont(font)

                painter.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, self._status_text)

            else:

                painter.setPen(QColor(80, 80, 80))

                painter.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, "No effect playing")

        # Draw status overlay on top of frame if set

        if self._status_text and self._frame and not self._frame.isNull():

            painter.setPen(QColor(255, 255, 255, 200))

            font = painter.font()

            font.setPointSize(10)

            painter.setFont(font)

            painter.drawText(self.rect().adjusted(8, 4, -8, -4),

                             Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft,

                             self._status_text)

        painter.end()





# ---------------------------------------------------------------------------

#  Fullscreen output window

# ---------------------------------------------------------------------------



class FullscreenOutputWindow(QWidget):

    """Borderless fullscreen window for displaying visualizer on a second monitor."""



    closed = pyqtSignal()



    def __init__(self, parent=None):

        super().__init__(parent, Qt.WindowType.FramelessWindowHint | Qt.WindowType.Tool)

        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)

        self.setStyleSheet("background-color: #000000;")

        self._canvas = VisualizerCanvas(self)

        layout = QVBoxLayout(self)

        layout.setContentsMargins(0, 0, 0, 0)

        layout.addWidget(self._canvas)



    @property

    def canvas(self) -> VisualizerCanvas:

        return self._canvas



    def set_frame(self, frame: QImage):

        self._canvas.set_frame(frame)



    def keyPressEvent(self, event):

        if event.key() == Qt.Key.Key_Escape:

            self.close()

        super().keyPressEvent(event)



    def closeEvent(self, event):

        self.closed.emit()

        super().closeEvent(event)





# ---------------------------------------------------------------------------

#  Video decoder (using OpenCV if available, fallback to QMediaPlayer stills)

# ---------------------------------------------------------------------------



class VideoDecoder:

    """Decodes video files frame-by-frame. Uses OpenCV if available.

    Supports an optional *max_size* (width, height) hint.  When the source
    video exceeds this, decoded frames are down-scaled with OpenCV before
    being converted to QImage – dramatically cheaper colour conversion,
    QImage creation, and downstream painting.

    Uses a double-buffered numpy array so QImage can reference the array
    directly without a per-frame ``.copy()`` — saving ~8 MB/frame of
    allocation and memcpy at 1080p.
    """



    def __init__(self, path: str, loop: bool = True,
                 max_size: tuple[int, int] | None = None,
                 target_size: tuple[int, int] | None = None):

        self.path = path

        self.loop = loop

        self._cap = None
        self._reader = None

        self._fps = 30.0

        self._frame_count = 0

        self._max_size = max_size  # (w, h) cap for decode output
        self._target_size = target_size  # (w, h) exact output size; letterbox with black

        self._width = 0

        self._height = 0

        self._cv2_available = False

        self._finished = False

        self._start_time: float | None = None  # set externally when play begins

        self._duration = 0.0  # total duration in seconds

        # Double-buffer: two numpy arrays so the previous frame stays
        # valid while the new one is being filled.  The QImage returned
        # by read_frame() references _np_bufs[_buf_idx^1] (the *previous*
        # write slot) whose memory remains stable until two frames later.
        self._np_bufs: list = [None, None]
        self._buf_idx: int = 0
        self._read_pos: int = 0  # internal frame-position counter (avoids slow cv2 GET)

        # Continuous background decode thread + frame queue so the
        # render timer never blocks on cv2.VideoCapture.read().
        import threading as _th, collections as _col
        self._frame_queue: _col.deque = _col.deque()
        self._queue_lock = _th.Lock()
        self._decode_thread: _th.Thread | None = None
        self._decode_stop = False
        self._seek_request: int = -1   # atomic; -1 = no pending seek
        self._last_delivered: QImage | None = None
        self._QUEUE_AHEAD = 6

        self._open()



    def _open(self):

        import os

        if not os.path.isfile(self.path):

            _viz_log(f"[VideoDecoder] File does not exist: {self.path}")

            return

        try:
            from ffmpeg_reader import FFmpegVideoReader
            self._reader = FFmpegVideoReader(self.path)
            if self._reader.width == 0 or self._reader.height == 0:
                _viz_log(f"[VideoDecoder] Failed to probe video: {self.path}")
                return
            if not self._reader.open():
                _viz_log(f"[VideoDecoder] Failed to open ffmpeg pipe: {self.path}")
                return

            self._fps = self._reader.fps
            self._frame_count = self._reader.frame_count
            self._width = self._reader.width
            self._height = self._reader.height
            self._duration = (
                self._frame_count / self._fps
                if self._fps > 0 and self._frame_count > 0
                else self._reader.duration
            )
            self._cv2_available = True  # still need cv2 for resize/cvtColor

            _viz_log(
                f"[VideoDecoder] Opened video (ffmpeg pipe): {self.path} "
                f"({self._width}x{self._height} @ {self._fps}fps, "
                f"{self._frame_count} frames, {self._duration:.1f}s)"
            )

        except Exception as e:

            _viz_log(f"[VideoDecoder] Error opening video {self.path}: {e}")

            import traceback

            _viz_log(f"[VideoDecoder] Traceback:\n{traceback.format_exc()}")



    @property

    def is_open(self) -> bool:

        reader = getattr(self, '_reader', None)
        if reader:
            return reader.isOpened()

        return False



    @property

    def finished(self) -> bool:

        return self._finished



    @property

    def fps(self) -> float:

        return self._fps



    # ---- background decode thread ------------------------------------------

    def _start_decode_thread(self):
        """Start the persistent background decode thread if not running."""
        if self._finished:
            return  # Video ended — don't restart the decode loop
        if self._decode_thread is not None and self._decode_thread.is_alive():
            return
        self._decode_stop = False
        import threading
        self._decode_thread = threading.Thread(target=self._decode_loop, daemon=True)
        self._decode_thread.start()

    def _stop_decode_thread(self):
        """Signal the decode thread to exit and wait for it."""
        self._decode_stop = True
        t = self._decode_thread
        if t is not None and t.is_alive():
            t.join(timeout=1.0)
        self._decode_thread = None

    def _decode_loop(self):
        """Continuously decode frames ahead into the frame queue."""
        import time as _time
        try:
            import cv2
            import numpy as np
        except ImportError:
            return

        reader = getattr(self, '_reader', None)
        if reader is None:
            _viz_log("[VideoDecoder] _decode_loop: reader is None, exiting thread")
            return

        _decode_frames_queued = 0
        _viz_log(f"[VideoDecoder] _decode_loop: starting, path={getattr(self, 'path', '?')}, fps={self._fps}, frame_count={self._frame_count}")

        try:
            while not self._decode_stop:
                # Handle pending seek request
                seek_to = self._seek_request
                if seek_to >= 0:
                    self._seek_request = -1
                    with self._queue_lock:
                        self._frame_queue.clear()
                    try:
                        reader.seek(seek_to)
                        self._read_pos = seek_to
                    except Exception:
                        pass
                    self._seeking_active = False   # pipe is (re)opened now
                    continue  # re-check immediately

                # Throttle when queue is full
                with self._queue_lock:
                    qlen = len(self._frame_queue)
                if qlen >= self._QUEUE_AHEAD:
                    _time.sleep(0.003)
                    continue

                if not reader.isOpened():
                    _viz_log(f"[VideoDecoder] _decode_loop: pipe closed (isOpened=False) at read_pos={self._read_pos}, loop={self.loop}, proc_poll={getattr(getattr(reader,'_proc',None),'poll',lambda:None)()}")
                    if self.loop and self._frame_count > 0:
                        # EOF while looping.  The ffmpeg process exits right
                        # after delivering the final frame, so isOpened()
                        # (which checks proc.poll() is None) flips to False
                        # *before* read() ever returns an EOF result.  In that
                        # case the `if not ret:` restart below never runs, so
                        # restart the pipe from frame 0 here instead.  Without
                        # this the video decoder thread would exit on the first
                        # loop and the second play would have audio but a frozen
                        # / blank video.
                        try:
                            reader.seek(0)
                            self._read_pos = 0
                            continue
                        except Exception as _restart_exc:
                            _viz_log(f"[VideoDecoder] _decode_loop: loop restart failed: {_restart_exc}")
                    if not self.loop:
                        self._finished = True
                    break

                pos = self._read_pos
                try:
                    ret, raw = reader.read()
                except Exception as _rd_exc:
                    _viz_log(f"[VideoDecoder] _decode_loop: read() exception at pos={pos}: {_rd_exc}")
                    break
                if not ret:
                    _viz_log(f"[VideoDecoder] _decode_loop: read() returned False at pos={pos}, loop={self.loop}, frame_count={self._frame_count}")
                    if self.loop and self._frame_count > 0:
                        try:
                            reader.seek(0)
                            self._read_pos = 0
                        except Exception:
                            break
                        continue
                    else:
                        self._finished = True
                        break
                self._read_pos = pos + 1

                # Resize + letterbox in OpenCV (cheaper than Qt)
                h0, w0 = raw.shape[:2]
                tw, th = (self._target_size or self._max_size or (w0, h0))
                if w0 != tw or h0 != th:
                    scale = min(tw / w0, th / h0)
                    new_w = max(1, int(w0 * scale))
                    new_h = max(1, int(h0 * scale))
                    interp = cv2.INTER_AREA if scale < 1 else cv2.INTER_LINEAR
                    raw = cv2.resize(raw, (new_w, new_h), interpolation=interp)
                    if new_w != tw or new_h != th:
                        canvas = np.zeros((th, tw, 3), dtype=np.uint8)
                        ox = (tw - new_w) // 2
                        oy = (th - new_h) // 2
                        canvas[oy:oy + new_h, ox:ox + new_w] = raw
                        raw = canvas

                frame_bgra = cv2.cvtColor(raw, cv2.COLOR_BGR2BGRA)
                h, w = frame_bgra.shape[:2]
                bpl = 4 * w
                # .copy() so QImage owns its data (thread-safe handoff)
                qimg = QImage(frame_bgra.data, w, h, bpl,
                              QImage.Format.Format_ARGB32).copy()

                with self._queue_lock:
                    self._frame_queue.append((pos, qimg))

                _decode_frames_queued += 1
                if _decode_frames_queued <= 3:
                    _viz_log(f"[VideoDecoder] _decode_loop: queued frame {pos} ({w}x{h}), total_queued={_decode_frames_queued}")

        except Exception as _loop_exc:
            import traceback as _tb
            _viz_log(f"[VideoDecoder] _decode_loop: EXCEPTION in loop body: {_loop_exc}\n{_tb.format_exc()}")
        finally:
            _viz_log(f"[VideoDecoder] _decode_loop: exiting, frames_queued={_decode_frames_queued}, _finished={self._finished}, _decode_stop={self._decode_stop}")

    # ---- frame read --------------------------------------------------------

    def read_frame(self, elapsed: float | None = None) -> QImage | None:
        """Return the correct frame for *elapsed* time, never blocking.

        A persistent background thread keeps a queue of decoded frames.
        This method pops the best match from that queue.  If the queue
        is empty it repeats the last delivered frame so the display
        never stutters.
        """
        if not self._cv2_available:
            return None
        reader = getattr(self, '_reader', None)
        if not reader or not reader.isOpened():
            # During loop restarts the ffmpeg pipe is briefly closed;
            # keep showing the last delivered frame instead of blanking.
            if self.loop and not self._finished and self._last_delivered is not None:
                return self._last_delivered
            return None

        # Ensure decode thread is running
        self._start_decode_thread()

        target_frame = -1
        if elapsed is not None and self._fps > 0 and self._frame_count > 0:
            if self.loop and self._duration > 0:
                elapsed = elapsed % self._duration
            target_frame = int(elapsed * self._fps)
            if target_frame >= self._frame_count:
                if self.loop:
                    target_frame = target_frame % self._frame_count
                else:
                    self._finished = True
                    return None

        with self._queue_lock:
            if not self._frame_queue:
                # Queue empty — repeat last frame, or None at startup
                if self._finished:
                    return None
                return self._last_delivered

            if target_frame >= 0:
                oldest = self._frame_queue[0][0]
                newest = self._frame_queue[-1][0]

                # Decide whether a real seek (ffmpeg pipe restart) is needed.
                # Restarting the pipe is expensive and clears the queue, so we
                # ONLY do it for genuine jumps:
                #   • Backward jump  (user scrubbed back before the buffer), or
                #   • Huge forward jump (user scrubbed far ahead — more than a
                #     few seconds past everything we've decoded).
                # A modest forward gap just means the decoder is lagging
                # (e.g. ffmpeg's ~1 s startup latency).  In that case we must
                # NOT seek — seeking forward here clears the queue before any
                # frame is delivered, which spirals into perpetual seeking and
                # a permanently black canvas.  Instead, deliver the newest
                # frame we have and let the decoder catch up to real time.
                big_fwd = int(self._fps * 3)
                if target_frame < oldest - 10 or target_frame > newest + big_fwd:
                    # Don't stack seeks.  If a pipe-restart is already in
                    # progress, wait for it to finish rather than issuing a
                    # fresh seek to an ever-larger target on every tick — the
                    # decoder would never catch up, spiralling into perpetual
                    # seeking that freezes the canvas on the last frame while
                    # audio keeps playing (looks "paused").  This happens most
                    # often right after a song switch, when GC + ffmpeg startup
                    # briefly push the decoder several seconds behind realtime.
                    if not self._seeking_active:
                        self._seek_request = target_frame
                        self._seeking_active = True   # cleared by decode loop
                    return self._last_delivered

                if target_frame >= newest:
                    # Decoder is behind — deliver the newest decoded frame and
                    # drop the older buffered ones to stay in sync with audio.
                    frame = None
                    while self._frame_queue:
                        _, frame = self._frame_queue.popleft()
                else:
                    # target is inside the buffered range — pick the closest
                    # frame and pop everything up to and including it.
                    best_idx = 0
                    best_dist = abs(self._frame_queue[0][0] - target_frame)
                    for i in range(1, len(self._frame_queue)):
                        d = abs(self._frame_queue[i][0] - target_frame)
                        if d < best_dist:
                            best_dist = d
                            best_idx = i
                    frame = None
                    for _ in range(best_idx + 1):
                        if self._frame_queue:
                            _, frame = self._frame_queue.popleft()
            else:
                # Sequential mode: just pop the next frame
                _, frame = self._frame_queue.popleft()

        if frame is not None:
            self._last_delivered = frame
        return self._last_delivered



    def seek(self, frame_number: int):
        reader = getattr(self, '_reader', None)
        if reader:
            self._seeking_active = True   # cleared by _decode_loop after pipe reopens
            self._seek_request = frame_number
            with self._queue_lock:
                self._frame_queue.clear()
            self._read_pos = frame_number

    def release(self):
        self._stop_decode_thread()
        with self._queue_lock:
            self._frame_queue.clear()
        self._last_delivered = None

        reader = getattr(self, '_reader', None)
        if reader:
            reader.release()
            self._reader = None
        self._np_bufs = [None, None]

    def __del__(self):
        self.release()


# ---------------------------------------------------------------------------
#  Video proxy — transcode to a lightweight format for smooth playback
# ---------------------------------------------------------------------------

# Module-level cache: original_path → proxy_path (survives engine restarts
# within the same session; proxy files live in the system temp folder).
_proxy_cache: dict[str, str] = {}


def _get_ffmpeg_exe() -> str | None:
    """Return the path to an ffmpeg executable, or None if unavailable."""
    # 1) imageio-ffmpeg (bundled static binary — most reliable)
    try:
        import imageio_ffmpeg
        p = imageio_ffmpeg.get_ffmpeg_exe()
        if p:
            return p
    except Exception:
        pass
    # 2) System PATH
    import shutil
    p = shutil.which("ffmpeg")
    return p


def _get_ffprobe_exe() -> str | None:
    """Return path to an ffprobe executable, or None."""
    # imageio-ffmpeg ships ffprobe alongside ffmpeg in the same binaries dir
    try:
        import imageio_ffmpeg, os
        ff = imageio_ffmpeg.get_ffmpeg_exe()
        if ff:
            d = os.path.dirname(ff)
            for name in ("ffprobe", "ffprobe.exe"):
                candidate = os.path.join(d, name)
                if os.path.isfile(candidate):
                    return candidate
    except Exception:
        pass
    import shutil
    return shutil.which("ffprobe")


def _probe_video(video_path: str) -> dict | None:
    """Use ffprobe (or ffmpeg -i) to get basic video info.  Returns dict with
    keys 'width', 'height', 'duration', 'codec' or None on failure."""
    import subprocess, json, re as _re

    # Try ffprobe first (structured JSON output)
    probe = _get_ffprobe_exe()
    if probe:
        try:
            cmd = [
                probe, "-v", "quiet",
                "-print_format", "json",
                "-show_streams", "-show_format",
                video_path,
            ]
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=15,
                               creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0))
            if r.returncode == 0:
                info = json.loads(r.stdout)
                for s in info.get("streams", []):
                    if s.get("codec_type") == "video":
                        return {
                            "width": int(s.get("width", 0)),
                            "height": int(s.get("height", 0)),
                            "codec": s.get("codec_name", ""),
                            "duration": float(info.get("format", {}).get("duration", 0)),
                        }
        except Exception:
            pass

    # Fallback: parse ffmpeg -i stderr (always available via imageio-ffmpeg)
    # IMPORTANT: Do NOT pass "-f null -" — that decodes the entire video!
    # Passing just "-i <file>" with no output makes ffmpeg print stream
    # info to stderr and exit immediately (rc=1, "no output specified").
    ffmpeg = _get_ffmpeg_exe()
    if ffmpeg:
        try:
            cmd = [ffmpeg, "-i", video_path, "-hide_banner"]
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=10,
                               creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0))
            # ffmpeg exits 1 ("must specify output") but prints info to stderr
            stderr = r.stderr or ""
            # Look for "Video: h264 ..., 1920x1080" pattern
            m = _re.search(r'Video:\s+(\w+).*?,\s+(\d{2,5})x(\d{2,5})', stderr)
            if m:
                codec = m.group(1).lower()
                w, h = int(m.group(2)), int(m.group(3))
                # Duration
                dur = 0.0
                dm = _re.search(r'Duration:\s+(\d+):(\d+):(\d+(?:\.\d+)?)', stderr)
                if dm:
                    dur = int(dm.group(1)) * 3600 + int(dm.group(2)) * 60 + float(dm.group(3))
                return {"width": w, "height": h, "codec": codec, "duration": dur}
        except Exception:
            pass

    return None


def _validate_video_file(video_path: str) -> str | None:
    """Return None if the video looks valid, or an error message string."""
    import os
    if not os.path.isfile(video_path):
        return f"File not found:\n{video_path}"
    info = _probe_video(video_path)
    if info is not None:
        if info["width"] == 0 or info["height"] == 0:
            return "File has no video stream or zero dimensions."
        return None  # OK
    return "Cannot decode this video file.\nTry a common format: MP4, AVI, MOV, MKV, WebM."


def _needs_proxy(video_path: str, target_w: int, target_h: int) -> bool:
    """Return True if the source video is expensive enough to warrant a proxy.

    Criteria: resolution exceeds the render target *or* codec is H.264/H.265
    (inter-frame prediction is slow to decode on weaker CPUs).
    """
    info = _probe_video(video_path)
    if info is not None:
        w, h, codec = info["width"], info["height"], info["codec"].lower()
        if w > target_w or h > target_h:
            return True
        # Proxy inter-frame codecs even at matching resolution.
        if any(tag in codec for tag in ('h264', 'h265', 'hevc', 'avc', 'vp9', 'av1')):
            return True
        if codec == "mjpeg":
            return False  # already intra-frame
        return False
    return False


def _proxy_path_for(src_path: str, target_w: int, target_h: int) -> str:
    """Deterministic proxy file path for a given source video."""
    import os, hashlib, tempfile
    h = hashlib.md5(f"{src_path}:{target_w}x{target_h}:v2".encode()).hexdigest()[:12]
    proxy_dir = os.path.join(tempfile.gettempdir(), "ld_video_proxies")
    os.makedirs(proxy_dir, exist_ok=True)
    return os.path.join(proxy_dir, f"proxy_{h}.mkv")


def _create_video_proxy(src_path: str, target_w: int, target_h: int,
                        progress_cb=None) -> str | None:
    """Transcode *src_path* to an MJPEG proxy at *target_w* x *target_h*.

    Uses FFmpeg → MKV container when available (proper frame index, handles
    virtually all input codecs).  Falls back to OpenCV → AVI.

    Returns the proxy file path, or None on failure.
    """
    import os
    if src_path in _proxy_cache:
        if os.path.isfile(_proxy_cache[src_path]):
            return _proxy_cache[src_path]

    proxy_path = _proxy_path_for(src_path, target_w, target_h)
    if os.path.isfile(proxy_path) and os.path.getsize(proxy_path) > 1024:
        _proxy_cache[src_path] = proxy_path
        _viz_log(f"[VideoProxy] Reusing cached proxy: {proxy_path}")
        return proxy_path

    # --- Try FFmpeg first (fast, supports all codecs) ---
    ffmpeg = _get_ffmpeg_exe()
    if ffmpeg:
        try:
            import subprocess
            cmd = [
                ffmpeg, "-y",
                "-i", src_path,
                "-vf", f"scale={target_w}:{target_h}:force_original_aspect_ratio=decrease,"
                       f"pad={target_w}:{target_h}:(ow-iw)/2:(oh-ih)/2:color=black",
                "-c:v", "mjpeg",
                "-q:v", "8",       # quality (2=best, 31=worst); 8 is a good balance
                "-an",             # drop audio (played separately)
                "-fps_mode", "cfr",
                proxy_path,
            ]
            _viz_log(f"[VideoProxy] FFmpeg transcoding: {src_path} -> {proxy_path}")
            r = subprocess.run(
                cmd, capture_output=True, text=True, timeout=1200,
                creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0),
            )
            if r.returncode == 0 and os.path.isfile(proxy_path) and os.path.getsize(proxy_path) > 1024:
                # Validate the proxy via ffprobe (avoids cv2.VideoCapture + FFmpeg DLL)
                _proxy_info = _probe_video(proxy_path)
                if _proxy_info is None or _proxy_info.get('width', 0) == 0:
                    _viz_log(f"[VideoProxy] Proxy unreadable by ffprobe, deleting: {proxy_path}")
                    os.remove(proxy_path)
                else:
                    _proxy_dur = _proxy_info.get('duration', 0)
                    # Duration sanity: compare proxy to source
                    _src_info = _probe_video(src_path)
                    _src_dur = _src_info.get('duration', 0) if _src_info else 0
                    if _src_dur > 5 and _proxy_dur > 0 and _proxy_dur < _src_dur * 0.5:
                        _viz_log(f"[VideoProxy] WARNING: Proxy is truncated! "
                                 f"proxy={_proxy_dur:.1f}s vs source={_src_dur:.1f}s — discarding")
                        os.remove(proxy_path)
                    else:
                        _proxy_cache[src_path] = proxy_path
                        _viz_log(f"[VideoProxy] FFmpeg transcode done ("
                                 f"{_proxy_dur:.1f}s): {proxy_path}")
                        return proxy_path
            else:
                _viz_log(f"[VideoProxy] FFmpeg failed (rc={r.returncode}): {r.stderr[-500:] if r.stderr else 'no stderr'}")
                # Clean up partial file
                if os.path.isfile(proxy_path):
                    os.remove(proxy_path)
        except Exception as exc:
            _viz_log(f"[VideoProxy] FFmpeg error: {exc}")

    # --- Fallback: OpenCV frame-by-frame ---
    # cv2.VideoWriter doesn't reliably write MKV, so use .avi for this path.
    fallback_path = proxy_path.replace('.mkv', '.avi')
    try:
        import cv2
        import numpy as np
        cap = cv2.VideoCapture(src_path)
        if not cap.isOpened():
            cap.release()
            return None
        fps = cap.get(cv2.CAP_PROP_FPS) or 30.0
        total = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
        src_w = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
        src_h = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))

        scale = min(target_w / max(src_w, 1), target_h / max(src_h, 1))
        new_w = max(1, int(src_w * scale))
        new_h = max(1, int(src_h * scale))
        ox = (target_w - new_w) // 2
        oy = (target_h - new_h) // 2

        fourcc = cv2.VideoWriter_fourcc(*'MJPG')
        writer = cv2.VideoWriter(fallback_path, fourcc, fps, (target_w, target_h))
        if not writer.isOpened():
            cap.release()
            _viz_log(f"[VideoProxy] cv2 writer failed for {fallback_path}")
            return None

        _viz_log(f"[VideoProxy] cv2 transcoding {src_w}x{src_h} -> {target_w}x{target_h}")
        count = 0
        while True:
            ret, frame = cap.read()
            if not ret:
                break
            if new_w != src_w or new_h != src_h:
                interp = cv2.INTER_AREA if scale < 1 else cv2.INTER_LINEAR
                frame = cv2.resize(frame, (new_w, new_h), interpolation=interp)
            if new_w != target_w or new_h != target_h:
                canvas = np.zeros((target_h, target_w, 3), dtype=np.uint8)
                canvas[oy:oy + new_h, ox:ox + new_w] = frame
                frame = canvas
            writer.write(frame)
            count += 1
            if progress_cb and total > 0 and count % 30 == 0:
                progress_cb(count / total)

        writer.release()
        cap.release()
        _viz_log(f"[VideoProxy] cv2 done — {count} frames -> {fallback_path}")
        _proxy_cache[src_path] = fallback_path
        return fallback_path
    except Exception as exc:
        _viz_log(f"[VideoProxy] Transcode error: {exc}")
        import traceback
        _viz_log(traceback.format_exc())
        return None


# ---------------------------------------------------------------------------

#  Video audio player — uses QMediaPlayer to play the audio track of a video

# ---------------------------------------------------------------------------



class _VideoAudioPlayer:
    """Plays the audio track of a video file using sounddevice + ffmpeg.

    All audio I/O runs on a background thread — no COM/WMF involvement on
    the main thread, so Windows focus events (WM_ACTIVATE) cannot deadlock.
    """

    _SAMPLE_RATE = 44100
    _CHANNELS = 2
    _CHUNK_FRAMES = 4096  # frames per sounddevice callback

    def __init__(self, video_path: str, loop: bool = False):
        self._video_path = video_path
        self._loop = loop
        self._volume = 1.0
        self._stop_event = threading.Event()
        self._paused = False
        self._thread: threading.Thread | None = None
        self._started = False
        self._sd = None   # sounddevice module, loaded lazily
        self._ffmpeg = None  # ffmpeg binary path
        self._current_proc = None  # ffmpeg subprocess; set by audio thread so stop() can terminate it
        _viz_log(f"[AudioPlayer] Ready: {video_path}  loop={loop}")

    def _find_ffmpeg(self) -> str | None:
        # 1) imageio-ffmpeg (bundled static binary — works in installer)
        try:
            import imageio_ffmpeg
            p = imageio_ffmpeg.get_ffmpeg_exe()
            if p and os.path.isfile(p):
                return p
        except Exception:
            pass
        import shutil
        p = shutil.which('ffmpeg')
        if p:
            return p
        try:
            from moviepy.config import FFMPEG_BINARY
            if os.path.isfile(FFMPEG_BINARY):
                return FFMPEG_BINARY
        except Exception:
            pass
        # Check app bundle path (PyInstaller)
        import sys
        bundle = getattr(sys, '_MEIPASS', None)
        if bundle:
            for name in ('ffmpeg.exe', 'ffmpeg'):
                cand = os.path.join(bundle, name)
                if os.path.isfile(cand):
                    return cand
        return None

    def _audio_thread(self, start_seconds: float = 0.0):
        """Background thread: ffmpeg→pipe→sounddevice stream."""
        try:
            import sounddevice as sd
            import numpy as np
            import subprocess
        except ImportError:
            _viz_log("[AudioPlayer] sounddevice/numpy not available — no audio")
            return

        ffmpeg_bin = self._find_ffmpeg()
        if not ffmpeg_bin:
            _viz_log("[AudioPlayer] ffmpeg not found — no audio")
            return

        sr = self._SAMPLE_RATE
        ch = self._CHANNELS
        bytes_per_frame = ch * 2  # int16

        while not self._stop_event.is_set():
            cmd = [
                ffmpeg_bin, '-hide_banner', '-loglevel', 'error',
                '-ss', str(start_seconds),  # seek to start position
                '-i', self._video_path,
                '-vn',               # skip video
                '-f', 's16le',       # raw signed 16-bit little-endian PCM
                '-ar', str(sr),
                '-ac', str(ch),
                'pipe:1',
            ]
            try:
                proc = subprocess.Popen(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.DEVNULL,
                    creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0),
                )
            except Exception as e:
                _viz_log(f"[AudioPlayer] ffmpeg launch error: {e}")
                raise  # propagates to threading.excepthook → Appertini

            self._current_proc = proc  # expose so stop() can terminate it
            chunk_bytes = self._CHUNK_FRAMES * bytes_per_frame
            # Pre-fill a queue of decoded PCM chunks.  A Python-level callback
            # drains the queue so that any PortAudio/cffi error surfaces as a
            # normal Python exception caught by our except block rather than
            # as an unraisable "Exception ignored" printed to stderr.
            import queue as _queue
            import time as _t2
            pcm_queue: _queue.Queue = _queue.Queue(maxsize=8)
            stream_error: list = []  # [Exception] if callback raises

            def _audio_callback(outdata, frames, time_info, status):
                try:
                    if status.output_underflow:
                        # Insert silence rather than raising
                        outdata[:] = 0
                        return
                    try:
                        chunk = pcm_queue.get_nowait()
                    except _queue.Empty:
                        outdata[:] = 0
                        return
                    if chunk is None:  # sentinel — stream should stop
                        outdata[:] = 0
                        raise sd.CallbackStop
                    # chunk is a numpy int16 array shaped (frames, ch); adjust if needed
                    n = min(len(chunk), len(outdata))
                    # Apply volume here (not at enqueue time) so slider changes
                    # take effect on the next callback block (~1 block latency).
                    vol = self._volume
                    if vol != 1.0:
                        chunk = (chunk[:n] * vol).clip(-32768, 32767).astype('int16')
                    outdata[:n] = chunk[:n]
                    if n < len(outdata):
                        outdata[n:] = 0
                except sd.CallbackStop:
                    raise
                except Exception as e:
                    # Do NOT raise from inside the CFFI callback — that causes
                    # the blank "Python-CFFI error" dialog on Windows.  Instead
                    # record the error, fill silence, and signal the reader loop
                    # to exit cleanly via the stop event.
                    stream_error.append(e)
                    outdata[:] = 0
                    self._stop_event.set()  # wake the reader loop
                    # Return normally; the outer loop will exit and report.

            def _open_output_stream():
                return sd.OutputStream(
                    samplerate=sr,
                    channels=ch,
                    dtype='int16',
                    blocksize=self._CHUNK_FRAMES,
                    callback=_audio_callback,
                )

            try:
                try:
                    _stream_cm = _open_output_stream()
                except Exception as _open_err:
                    # After the machine sits idle / sleeps (e.g. overnight),
                    # Windows re-powers the audio endpoints and PortAudio's
                    # cached device handles go stale, so the first open fails.
                    # Re-initialise PortAudio to flush the stale state and retry
                    # once so playback recovers without an app restart.
                    _viz_report_error(_open_err, "audio_stream_open_retry")
                    try:
                        sd._terminate()
                        sd._initialize()
                    except Exception:
                        pass
                    _stream_cm = _open_output_stream()
                with _stream_cm as stream:
                    while not self._stop_event.is_set():
                        if self._paused:
                            _t2.sleep(0.02)
                            continue
                        if stream_error:
                            err = stream_error[0]
                            _viz_report_error(err, "audio_callback")
                            break  # exit cleanly; don't re-raise through CFFI
                        raw = proc.stdout.read(chunk_bytes)
                        if not raw:
                            # EOF — push sentinel and wait briefly for drain
                            try:
                                pcm_queue.put(None, timeout=1.0)
                            except _queue.Full:
                                pass
                            break
                        arr = np.frombuffer(raw, dtype='int16').reshape(-1, ch)
                        try:
                            pcm_queue.put(arr, timeout=1.0)
                        except _queue.Full:
                            # Queue blocked — stream stalled (e.g. after sleep)
                            _viz_log("[AudioPlayer] PCM queue stall — stream likely broken")
                            break
                    # Let the callback drain remaining queued chunks
                    _t2.sleep(0.1)
            except Exception as e:
                # PortAudioError on stream open (device power-save, device
                # change, etc.) — log and report to Appertini without
                # re-raising, so the CFFI layer never sees an unhandled
                # exception (which would show the blank error dialog).
                _viz_report_error(e, "audio_stream")
            finally:
                try:
                    proc.stdout.close()
                    proc.terminate()
                    proc.wait(timeout=2)
                except Exception:
                    pass
                self._current_proc = None

            if not self._loop or self._stop_event.is_set():
                break
            # Brief pause between loop iterations so the audio device driver
            # has time to release the previous stream before we open a new one.
            # Without this, PortAudio sometimes fails to reopen on Windows,
            # producing a blank "Python-CFFI error" dialog.
            _t2.sleep(0.25)
            start_seconds = 0.0  # restart from beginning on each loop

    def play(self, start_seconds: float = 0.0):
        if self._started:
            return
        self._started = True
        self._stop_event.clear()
        self._thread = threading.Thread(
            target=self._audio_thread, args=(start_seconds,),
            daemon=True, name="viz-audio")
        self._thread.start()
        _viz_log("[AudioPlayer] play() — background thread started")

    def seek(self, seconds: float):
        """Restart audio from the given position."""
        self.stop()
        self._started = False
        self.play(start_seconds=seconds)

    def stop(self):
        self._stop_event.set()
        # Terminate the ffmpeg process to unblock proc.stdout.read() immediately,
        # allowing the audio thread to exit cleanly rather than waiting up to
        # 1+ seconds for a read timeout before noticing the stop event.
        proc = getattr(self, '_current_proc', None)
        if proc is not None:
            try:
                proc.terminate()
            except Exception:
                pass
            self._current_proc = None
        if self._thread and self._thread.is_alive():
            self._thread.join(timeout=2.0)
        self._thread = None

    def set_volume(self, vol: float):
        self._volume = max(0.0, min(1.0, vol))

    def pause(self):
        """Pause audio output (audio thread loops on ``self._paused``)."""
        self._paused = True

    def resume(self):
        """Resume audio output after pause()."""
        self._paused = False

    def release(self):
        self.stop()



# ---------------------------------------------------------------------------
#  NDI audio extractor — decodes audio from a video file using ffmpeg
# ---------------------------------------------------------------------------

def _find_ffmpeg_binary() -> str | None:
    """Locate an ffmpeg executable for audio extraction."""
    import shutil
    # 1. System PATH
    p = shutil.which('ffmpeg')
    if p:
        return p
    # 2. moviepy's bundled ffmpeg
    try:
        from moviepy.config import FFMPEG_BINARY
        if os.path.isfile(FFMPEG_BINARY):
            return FFMPEG_BINARY
    except Exception:
        pass
    return None


class _NDIAudioExtractor:
    """Extracts audio from a video file into a planar float32 numpy buffer.

    Extraction runs in a background thread.  Once complete, ``read_chunk``
    returns the PCM slice for a given elapsed time.
    """

    NDI_SAMPLE_RATE = 48000
    NDI_CHANNELS = 2  # stereo

    def __init__(self, video_path: str):
        self._ready = False
        self._audio_data = None  # numpy float32, shape (N, channels)
        self._sample_rate = self.NDI_SAMPLE_RATE
        self._channels = self.NDI_CHANNELS
        self._duration = 0.0
        self._proc = None  # subprocess.Popen handle for cleanup
        self._released = False
        self._thread = threading.Thread(
            target=self._extract, args=(video_path,), daemon=True
        )
        self._thread.start()

    # ---- background extraction -------------------------------------------

    def _extract(self, video_path: str):
        import subprocess
        ffmpeg = _find_ffmpeg_binary()
        if not ffmpeg:
            _viz_log("[NDIAudio] ffmpeg not found — NDI audio disabled for this clip")
            return
        try:
            proc = subprocess.Popen(
                [
                    ffmpeg,
                    '-i', video_path,
                    '-f', 'f32le',
                    '-acodec', 'pcm_f32le',
                    '-ac', str(self._channels),
                    '-ar', str(self._sample_rate),
                    '-v', 'quiet',
                    '-',
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0),
            )
            self._proc = proc
            try:
                stdout, _ = proc.communicate(timeout=120)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.communicate()
                _viz_log("[NDIAudio] ffmpeg extraction timed out")
                return
            finally:
                self._proc = None

            if self._released:
                return  # release() was called while extracting

            if proc.returncode == 0 and len(stdout) > 0:
                import numpy as np
                self._audio_data = (
                    np.frombuffer(stdout, dtype=np.float32)
                    .reshape(-1, self._channels)
                    .copy()
                )
                self._duration = len(self._audio_data) / self._sample_rate
                self._ready = True
                _viz_log(
                    f"[NDIAudio] Extracted {self._duration:.1f}s audio "
                    f"({len(self._audio_data)} samples, {self._channels}ch, "
                    f"{self._sample_rate}Hz)"
                )
            else:
                _viz_log("[NDIAudio] No audio track in video (or ffmpeg error)")
        except Exception as exc:
            _viz_log(f"[NDIAudio] Extraction failed: {exc}")

    # ---- chunk reading ---------------------------------------------------

    @property
    def ready(self) -> bool:
        return self._ready

    def read_chunk(
        self, elapsed: float, duration: float, loop: bool = False
    ) -> tuple[bytes | None, int]:
        """Return ``(planar_bytes, samples_per_channel)`` for the time window.

        *planar_bytes* is laid out channel-by-channel for NDI (ch0 samples
        followed by ch1 samples).  Returns ``(None, 0)`` if not ready or no
        audio data.
        """
        if not self._ready or self._audio_data is None:
            return None, 0

        import numpy as np

        total = len(self._audio_data)
        ad = self._duration

        if loop and ad > 0:
            elapsed = elapsed % ad

        start = int(elapsed * self._sample_rate)
        count = int(duration * self._sample_rate)

        if start >= total:
            return None, 0

        end = min(start + count, total)
        chunk = self._audio_data[start:end]  # shape (N, channels)

        if len(chunk) == 0:
            return None, 0

        # Convert interleaved → planar for NDI audio frame v2
        planar = np.ascontiguousarray(chunk.T)  # shape (channels, N)
        return planar.tobytes(), chunk.shape[0]

    # ---- cleanup ---------------------------------------------------------

    def release(self):
        self._released = True
        self._audio_data = None
        self._ready = False
        # Kill the ffmpeg subprocess if it's still running
        proc = self._proc
        if proc is not None:
            try:
                proc.kill()
            except Exception:
                pass


# ---------------------------------------------------------------------------

#  Spatial DMX mapper — samples a frame and sets fixture colors

# ---------------------------------------------------------------------------



class SpatialDMXMapper:

    """Maps regions of a rendered frame to fixture RGB channels based on

    fixture stage positions (location_x, location_y in 0.0–1.0)."""

    # Pre-computed sRGB ↔ linear lookup tables (shared across instances).
    # Screen pixels are in sRGB space; LEDs respond ~linearly to DMX.
    # Averaging must happen in linear space, then convert back to sRGB
    # for correct perceptual colour matching on the fixtures.
    _SRGB_TO_LINEAR: list[float] = []  # 256 entries: sRGB byte → linear float
    _LINEAR_TO_SRGB: list[int] = []    # 1024 entries: linear float *1023 → sRGB byte

    @classmethod
    def _build_gamma_luts(cls):
        """Build the lookup tables once on first use."""
        if cls._SRGB_TO_LINEAR:
            return
        import math
        # sRGB → linear
        lut_fwd = []
        for i in range(256):
            v = i / 255.0
            if v <= 0.04045:
                lut_fwd.append(v / 12.92)
            else:
                lut_fwd.append(((v + 0.055) / 1.055) ** 2.4)
        cls._SRGB_TO_LINEAR = lut_fwd
        # linear → sRGB (1024-entry inverse table for fast lookup)
        lut_inv = []
        for i in range(1024):
            v = i / 1023.0
            if v <= 0.0031308:
                s = v * 12.92
            else:
                s = 1.055 * (v ** (1.0 / 2.4)) - 0.055
            lut_inv.append(max(0, min(255, int(s * 255.0 + 0.5))))
        cls._LINEAR_TO_SRGB = lut_inv

    def __init__(self):

        self._enabled = False

        self._fixtures: list = []

        self._artnet = None

        self._sample_radius = 0.05  # radius around fixture position to average

        # Set of (universe, 1-indexed channel) that this mapper actively writes.

        # Exposed so the effect engine can avoid clobbering visualizer output.

        self.controlled_channels: set[tuple[int, int]] = set()

        # Ensure gamma LUTs are ready
        self._build_gamma_luts()



    @property

    def enabled(self) -> bool:

        return self._enabled



    @enabled.setter

    def enabled(self, value: bool):

        self._enabled = value

        if not value:

            self.zero_channels()

    def zero_channels(self):
        """Zero all DMX channels currently controlled by this mapper, then clear the set."""
        if self._artnet and self.controlled_channels:
            for uni_idx, ch_addr in self.controlled_channels:
                uni = self._artnet.get_universe(uni_idx)
                if uni:
                    uni.set_channel(ch_addr, 0)
        self.controlled_channels.clear()

    def configure(self, fixtures: list, artnet_output):

        """Set the fixture list and art-net output to use."""

        self._fixtures = fixtures

        self._artnet = artnet_output



    def map_frame(self, frame: QImage):

        """Sample the frame at each fixture's position and send RGB to DMX.

        Uses a raw-bytes approach instead of per-pixel QImage.pixel() calls
        to avoid the massive Python/C++ crossing overhead that was freezing
        the app when videos played at 30 fps.
        """

        if not self._enabled or not self._artnet or not self._fixtures:

            return

        if frame is None or frame.isNull():

            return



        fw = frame.width()

        fh = frame.height()

        if fw < 1 or fh < 1:

            return

        # Convert to ARGB32 once so we know the exact byte layout.
        # On little-endian (Windows) pixel order in memory is B-G-R-A.
        if frame.format() != QImage.Format.Format_ARGB32:
            frame = frame.convertToFormat(QImage.Format.Format_ARGB32)
        bpl = frame.bytesPerLine()
        bits = frame.constBits()
        if bits is None:
            return
        # sip returns a voidptr; cast to a memoryview-compatible buffer
        try:
            buf = bits.asarray(fh * bpl)
        except Exception:
            return

        # Smaller radius: 2 % instead of 5 % — still enough for colour
        # blending but 6× fewer samples per fixture.
        radius_frac = 0.02

        # Rebuild controlled-channel set each frame so it stays in sync
        # with fixture list changes without extra bookkeeping.
        new_controlled: set[tuple[int, int]] = set()

        for fixture in self._fixtures:

            fx = getattr(fixture, 'location_x', 0.5)

            fy = getattr(fixture, 'location_y', 0.5)

            profile = getattr(fixture, 'profile', None)

            if not profile:

                continue

            # Pre-classify fixture: color wheel vs RGB
            mode_name = getattr(fixture, 'mode_name', '')
            channels = []
            if hasattr(profile, 'modes') and mode_name in profile.modes:
                channels = profile.modes[mode_name]
            elif hasattr(profile, 'channels'):
                channels = profile.channels
            ch_types = {(ch.type if hasattr(ch, 'type') else '') for ch in channels}
            has_rgb = 'red' in ch_types and 'green' in ch_types and 'blue' in ch_types
            has_wheel = 'color_wheel' in ch_types
            is_wheel_fixture = has_wheel and not has_rgb

            # --- Determine sampling region ---
            if is_wheel_fixture:
                # Use the full visual footprint of the drawn fixture icon
                vw = getattr(fixture, 'visual_width', 0.1)
                vh = getattr(fixture, 'visual_height', 0.05)
                x0 = max(0, int((fx - vw / 2) * (fw - 1)))
                x1 = min(fw, int((fx + vw / 2) * (fw - 1)) + 1)
                y0 = max(0, int((fy - vh / 2) * (fh - 1)))
                y1 = min(fh, int((fy + vh / 2) * (fh - 1)) + 1)
                # Use a larger step for the bigger area to keep it fast
                step = max(2, min((x1 - x0), (y1 - y0)) // 12)
            else:
                # Small radius for RGB fixtures (precise per-fixture color)
                px = int(fx * (fw - 1))
                py = int(fy * (fh - 1))
                radius_px = max(1, int(radius_frac * min(fw, fh)))
                x0 = max(0, px - radius_px)
                x1 = min(fw, px + radius_px + 1)
                y0 = max(0, py - radius_px)
                y1 = min(fh, py + radius_px + 1)
                step = 2

            r_lin, g_lin, b_lin, count = 0.0, 0.0, 0.0, 0
            s2l = self._SRGB_TO_LINEAR

            if is_wheel_fixture:
                # --- Dominant-color sampling for color wheel fixtures ---
                # Import colour utilities once
                try:
                    from .effect_engine import hex_to_rgb, color_distance, rgb_to_hex
                except ImportError:
                    from effect_engine import hex_to_rgb, color_distance, rgb_to_hex

                # Collect wheel colours from the fixture's color_wheel channel
                wheel_entries = []  # list of (rgb_tuple, dmx_value)
                for ch in channels:
                    if (ch.type if hasattr(ch, 'type') else '') == 'color_wheel':
                        for wc in getattr(ch, 'color_wheel_colors', []):
                            wc_rgb = hex_to_rgb(wc.get('color', '#ffffff'))
                            wheel_entries.append((wc_rgb, wc.get('value', 0)))
                        break

                # Pre-compute hue for each wheel entry (0-360, or -1 for achromatic)
                def _rgb_to_hue(r, g, b):
                    hi = max(r, g, b)
                    lo = min(r, g, b)
                    c = hi - lo
                    if c == 0 or hi == 0:
                        return -1.0  # achromatic
                    if hi == r:
                        h = ((g - b) / c) % 6.0
                    elif hi == g:
                        h = (b - r) / c + 2.0
                    else:
                        h = (r - g) / c + 4.0
                    return h * 60.0

                wheel_hues = []  # parallel to wheel_entries
                for (wr, wg, wb), _wval in wheel_entries:
                    wheel_hues.append(_rgb_to_hue(wr, wg, wb))

                _PIX_DARK = 40  # per-pixel brightness cutoff
                # Bucket: index into wheel_entries → vote count + brightness sum
                votes = {}  # {wheel_index: [count, brightness_sum]}
                l2s = self._LINEAR_TO_SRGB

                # Find a "white" / "open" wheel entry for achromatic pixels
                white_idx = -1
                for wi, (wrgb, _wval) in enumerate(wheel_entries):
                    # Treat any very light, low-saturation entry as "white"
                    wr, wg, wb = wrgb
                    if min(wr, wg, wb) > 200:
                        white_idx = wi
                        break

                for sy in range(y0, y1, step):
                    row_off = sy * bpl
                    for sx in range(x0, x1, step):
                        off = row_off + sx * 4  # BGRA layout
                        pb = buf[off]
                        pg = buf[off + 1]
                        pr = buf[off + 2]
                        hi = max(pr, pg, pb)
                        # Skip dark pixels entirely
                        if hi < _PIX_DARK:
                            continue
                        lo = min(pr, pg, pb)
                        # Saturation check: if the pixel is achromatic
                        # (spread between channels < 25% of brightness),
                        # vote for white or skip entirely
                        if (hi - lo) < hi * 0.25:
                            if white_idx >= 0:
                                if white_idx in votes:
                                    votes[white_idx][0] += 1
                                    votes[white_idx][1] += hi
                                else:
                                    votes[white_idx] = [1, hi]
                            continue
                        # Hue-based matching for chromatic pixels
                        pix_hue = _rgb_to_hue(pr, pg, pb)
                        best_idx = -1
                        best_dist = 181.0  # max possible hue gap is 180
                        for wi, wh in enumerate(wheel_hues):
                            if wh < 0:
                                continue  # skip achromatic wheel entries
                            diff = abs(pix_hue - wh)
                            if diff > 180.0:
                                diff = 360.0 - diff
                            if diff < best_dist:
                                best_dist = diff
                                best_idx = wi
                        if best_idx >= 0:
                            if best_idx in votes:
                                votes[best_idx][0] += 1
                                votes[best_idx][1] += hi
                            else:
                                votes[best_idx] = [1, hi]

                # Pick the wheel color with the most pixel votes
                if votes:
                    dominant_idx = max(votes, key=lambda k: votes[k][0])
                    dominant_count, dominant_bright_sum = votes[dominant_idx]
                    avg_brightness = int(dominant_bright_sum / dominant_count + 0.5)
                    dominant_dmx = wheel_entries[dominant_idx][1]
                else:
                    # No lit pixels at all → light off
                    avg_brightness = 0
                    dominant_dmx = 0

                # Also compute overall average for RGB path fallback (not used here
                # but keeps r_avg/g_avg/b_avg valid for the code below)
                r_avg = g_avg = b_avg = 0
                # Skip the normal averaging section
                count = -1  # sentinel so the shared average block is skipped

            else:
                # --- Normal averaging for RGB fixtures ---
                for sy in range(y0, y1, step):
                    row_off = sy * bpl
                    for sx in range(x0, x1, step):
                        off = row_off + sx * 4  # BGRA layout
                        b_lin += s2l[buf[off]]
                        g_lin += s2l[buf[off + 1]]
                        r_lin += s2l[buf[off + 2]]
                        count += 1



            if count == 0:

                continue

            if count > 0:
                # Average in linear space, convert back to sRGB for DMX
                l2s = self._LINEAR_TO_SRGB
                r_avg = l2s[min(1023, int(r_lin / count * 1023.0 + 0.5))]
                g_avg = l2s[min(1023, int(g_lin / count * 1023.0 + 0.5))]
                b_avg = l2s[min(1023, int(b_lin / count * 1023.0 + 0.5))]



            # Find RGB channels in fixture profile and set DMX values

            uni_idx = getattr(fixture, 'universe', 1)  # use directly (matches rest of app)

            addr = getattr(fixture, 'address', 1)

            uni = self._artnet.get_universe(uni_idx)

            # ---- Color-wheel-only fixture path ----
            if is_wheel_fixture:
                # dominant_dmx and avg_brightness were computed during sampling
                for i, ch in enumerate(channels):
                    ch_type = ch.type if hasattr(ch, 'type') else ''
                    channel_addr = addr + i
                    if ch_type == 'color_wheel':
                        uni.set_channel(channel_addr, dominant_dmx)
                        new_controlled.add((uni_idx, channel_addr))
                    elif ch_type == 'dimmer':
                        uni.set_channel(channel_addr, avg_brightness)
                        new_controlled.add((uni_idx, channel_addr))
                    elif ch_type == 'shutter':
                        uni.set_channel(channel_addr, 255 if avg_brightness > 0 else 0)
                        new_controlled.add((uni_idx, channel_addr))

            # ---- RGB fixture path (existing behaviour) ----
            else:
                for i, ch in enumerate(channels):

                    ch_type = ch.type if hasattr(ch, 'type') else ''

                    channel_addr = addr + i

                    if ch_type == 'red':

                        uni.set_channel(channel_addr, r_avg)

                        new_controlled.add((uni_idx, channel_addr))

                    elif ch_type == 'green':

                        uni.set_channel(channel_addr, g_avg)

                        new_controlled.add((uni_idx, channel_addr))

                    elif ch_type == 'blue':

                        uni.set_channel(channel_addr, b_avg)

                        new_controlled.add((uni_idx, channel_addr))

                    elif ch_type == 'dimmer':

                        brightness = max(r_avg, g_avg, b_avg)

                        uni.set_channel(channel_addr, brightness)

                        new_controlled.add((uni_idx, channel_addr))

                    elif ch_type == 'shutter':

                        uni.set_channel(channel_addr, 255)

                        new_controlled.add((uni_idx, channel_addr))



            # Handle pixel fixtures (LED bars / matrices)

            if getattr(profile, 'is_pixel_fixture', False):

                self._map_pixel_fixture(fixture, profile, buf, bpl, fw, fh, uni)

                # Register pixel channels as controlled
                pixel_table = getattr(profile, 'pixel_channel_table', None)
                if pixel_table:
                    for pixel_entry in pixel_table:
                        if isinstance(pixel_entry, dict):
                            for key in ('red', 'green', 'blue', 'white', 'dimmer'):
                                if key in pixel_entry:
                                    new_controlled.add((uni_idx, addr + pixel_entry[key]))
                        else:
                            ch_per_pixel = getattr(profile, 'channels_per_pixel', 3)
                            paddr = addr + pixel_entry
                            for j in range(min(ch_per_pixel, 4)):
                                new_controlled.add((uni_idx, paddr + j))

        self.controlled_channels = new_controlled



    def _map_pixel_fixture(self, fixture, profile, buf, bpl: int, fw: int, fh: int, uni):

        """Map portions of the frame to individual pixels of a pixel fixture.

        Uses a pre-converted ARGB32 raw buffer (BGRA byte order on
        little-endian) for fast sampling instead of QImage.pixel().
        """

        rows = getattr(profile, 'pixel_rows', 1)

        cols = getattr(profile, 'pixel_columns', 1)

        ch_per_pixel = getattr(profile, 'channels_per_pixel', 3)

        pixel_table = getattr(profile, 'pixel_channel_table', None)



        if not pixel_table:

            return



        fx = getattr(fixture, 'location_x', 0.5)

        fy = getattr(fixture, 'location_y', 0.5)

        vw = getattr(fixture, 'visual_width', 0.1)

        vh = getattr(fixture, 'visual_height', 0.05)



        for row in range(rows):

            for col in range(cols):

                # Position of this pixel in normalized coordinates

                px_norm_x = fx - vw / 2 + (col + 0.5) / max(cols, 1) * vw

                px_norm_y = fy - vh / 2 + (row + 0.5) / max(rows, 1) * vh



                # Sample the frame at this position via raw buffer

                sx = int(max(0, min(fw - 1, px_norm_x * (fw - 1))))

                sy = int(max(0, min(fh - 1, px_norm_y * (fh - 1))))

                off = sy * bpl + sx * 4  # BGRA byte order
                s2l = self._SRGB_TO_LINEAR
                l2s = self._LINEAR_TO_SRGB
                b_val = l2s[min(1023, int(s2l[buf[off]] * 1023.0 + 0.5))]
                g_val = l2s[min(1023, int(s2l[buf[off + 1]] * 1023.0 + 0.5))]
                r_val = l2s[min(1023, int(s2l[buf[off + 2]] * 1023.0 + 0.5))]



                # Get channel offset for this pixel

                pixel_idx = row * cols + col

                if pixel_idx < len(pixel_table):

                    pixel_entry = pixel_table[pixel_idx]

                    base_addr = getattr(fixture, 'address', 1)

                    if isinstance(pixel_entry, dict):

                        # Dict format: {"red": offset, "green": offset, "blue": offset, ...}

                        if 'red' in pixel_entry:

                            uni.set_channel(base_addr + pixel_entry['red'], r_val)

                        if 'green' in pixel_entry:

                            uni.set_channel(base_addr + pixel_entry['green'], g_val)

                        if 'blue' in pixel_entry:

                            uni.set_channel(base_addr + pixel_entry['blue'], b_val)

                        if 'white' in pixel_entry:

                            uni.set_channel(base_addr + pixel_entry['white'], max(r_val, g_val, b_val))

                        if 'dimmer' in pixel_entry:

                            uni.set_channel(base_addr + pixel_entry['dimmer'], max(r_val, g_val, b_val))

                    else:

                        # Simple int offset format

                        addr = base_addr + pixel_entry

                        if ch_per_pixel >= 3:

                            uni.set_channel(addr, r_val)

                            uni.set_channel(addr + 1, g_val)

                            uni.set_channel(addr + 2, b_val)

                            if ch_per_pixel >= 4:

                                uni.set_channel(addr + 3, max(r_val, g_val, b_val))





# ---------------------------------------------------------------------------

#  Main Visualizer Engine — orchestrates rendering, playback, mapping

# ---------------------------------------------------------------------------



class VisualizerEngine(QObject):

    """Main engine that renders effects/video, updates canvases, and maps to DMX."""



    frame_ready = pyqtSignal(QImage)  # emitted on each rendered frame
    playback_finished = pyqtSignal(str)  # emitted when a non-looping item finishes (item_id)
    position_changed = pyqtSignal(float, float)  # (position_seconds, duration_seconds)
    effect_overlay_changed = pyqtSignal(bool)  # True = effect overlay started, False = cleared



    def __init__(self, parent=None):

        super().__init__(parent)

        # Active playback state

        self._active_item: VisualizerItem | None = None

        self._active_effect: BaseVisualEffect | None = None

        self._video_decoder: VideoDecoder | None = None

        # Two-layer overlay: song plays on the bottom, effect overlays on top.
        # When an effect item is played while a song is active, the song keeps
        # running (audio + decoder) and the effect renders over it.
        self._song_layer_item: VisualizerItem | None = None
        self._effect_overlay_item: VisualizerItem | None = None

        self._ndi_receiver = None  # NDIReceiver for live input
        self._usb_receiver = None   # USBCaptureReceiver for HDMI/USB input

        self._audio_player: _VideoAudioPlayer | None = None
        self._audio_duration: float = 0.0  # duration for audio-only items

        self._start_time: float = 0.0

        self._playing: bool = False

        # Background proxy transcoding state
        self._proxy_thread: "threading.Thread | None" = None
        self._proxy_pending_item: VisualizerItem | None = None
        self._proxy_check_timer: QTimer | None = None



        # Render settings

        self._render_width = 1280

        self._render_height = 720

        self._target_fps = 30

        # GPU offscreen effect renderer — available but not used by default.
        # Can be enabled on systems where offloading rendering to the GPU
        # frees CPU for other tasks (DMX, effect engine, etc.).
        self._gpu_renderer: _GPUOffscreenRenderer | None = None



        # Fader-controlled brightness level (0.0–1.0).  When a visualizer
        # item is assigned to a fader, the GUI sets this so the render
        # pipeline dims the output proportionally.
        self._fader_level: float = 1.0

        # Canvases

        self._preview_canvas: VisualizerCanvas | None = None

        self._fullscreen_window: FullscreenOutputWindow | None = None



        # NDI output

        self._ndi_sender = None  # lazy — created by start_ndi()

        self._ndi_keepalive_timer = QTimer(self)

        self._ndi_keepalive_timer.setTimerType(Qt.TimerType.CoarseTimer)

        self._ndi_keepalive_timer.timeout.connect(self._ndi_keepalive_tick)

        self._ndi_black_frame: QImage | None = None

        self._ndi_audio_enabled: bool = False  # toggled from settings
        self._ndi_audio_extractor: _NDIAudioExtractor | None = None

        # NDI health monitor — periodically checks the sender and
        # auto-reconnects when it detects consecutive send failures.
        self._ndi_health_timer = QTimer(self)
        self._ndi_health_timer.setTimerType(Qt.TimerType.CoarseTimer)
        self._ndi_health_timer.timeout.connect(self._ndi_health_check)
        self._ndi_source_name: str = "Lighting Designer Visualizer"
        self._ndi_bind_ip: str = ""
        self._ndi_compress: str = "none"

        # ---- SRT output state ----
        self._srt_sender = None          # SRTSender instance or None
        self._srt_keepalive_timer = QTimer(self)
        self._srt_keepalive_timer.setTimerType(Qt.TimerType.CoarseTimer)
        self._srt_keepalive_timer.setInterval(500)
        self._srt_keepalive_timer.timeout.connect(self._srt_keepalive_tick)
        self._srt_black_frame: QImage | None = None
        self._srt_start_error: str = ""

        # DMX mapping

        self.spatial_mapper = SpatialDMXMapper()

        # Project fixtures — set by the GUI so fixture-aware effects
        # can access positions even when DMX mapping is not active.
        self._project_fixtures: list = []



        # Render timer (runs on Qt event loop)

        self._render_timer = QTimer(self)

        self._render_timer.setTimerType(Qt.TimerType.PreciseTimer)

        self._render_timer.timeout.connect(self._render_tick)



        # Items and pages storage (references to project data)

        self._items: dict[str, VisualizerItem] = {}

        self._pages: list[VisualizerPage] = []



    # -- Properties --



    @property

    def is_playing(self) -> bool:

        return self._playing



    @property

    def active_item(self) -> VisualizerItem | None:

        return self._active_item



    @property

    def render_size(self) -> tuple[int, int]:

        return (self._render_width, self._render_height)



    @render_size.setter

    def render_size(self, size: tuple[int, int]):

        self._render_width = max(64, size[0])

        self._render_height = max(36, size[1])



    @property

    def target_fps(self) -> int:

        return self._target_fps



    @target_fps.setter

    def target_fps(self, fps: int):

        self._target_fps = max(1, min(120, fps))

        if self._render_timer.isActive():

            self._render_timer.setInterval(1000 // self._target_fps)

    def get_position(self) -> float:
        """Return current playback position in seconds."""
        if not self._playing:
            return 0.0
        t = time.time() - self._start_time
        # Wrap position for looping videos so TC resets at each loop
        if self._active_item and getattr(self._active_item, 'loop', False):
            dur = self.get_duration()
            if dur > 0:
                t = t % dur
        return t

    def get_duration(self) -> float:
        """Return playback duration of current item in seconds (0 for effects/live).

        When a trim_end is set on the active item it acts as the effective
        duration — playback stops at that position rather than at the natural
        end of the file.
        """
        nat_dur = 0.0
        if self._video_decoder and hasattr(self._video_decoder, '_duration'):
            nat_dur = self._video_decoder._duration
        elif self._audio_duration > 0:
            nat_dur = self._audio_duration
        # Apply trim_end if set and less than the natural duration.
        trim_end = getattr(self._active_item, 'trim_end', 0.0) if self._active_item else 0.0
        if trim_end and 0 < trim_end < nat_dur:
            return trim_end
        return nat_dur

    @staticmethod
    def _probe_audio_duration(path: str) -> float:
        """Return duration in seconds of an audio/video file via ffmpeg probe."""
        try:
            import subprocess, re, os
            # Try imageio-ffmpeg first (bundled binary works in installer)
            ffmpeg_bin = None
            try:
                import imageio_ffmpeg
                p = imageio_ffmpeg.get_ffmpeg_exe()
                if p and os.path.isfile(p):
                    ffmpeg_bin = p
            except Exception:
                pass
            if not ffmpeg_bin:
                import shutil
                ffmpeg_bin = shutil.which('ffmpeg') or shutil.which('ffprobe')
            if not ffmpeg_bin:
                return 0.0
            result = subprocess.run(
                [ffmpeg_bin, '-hide_banner', '-i', path],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                timeout=8,
                creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0),
            )
            text = result.stderr.decode('utf-8', errors='replace')
            # Match "Duration: HH:MM:SS.ss"
            m = re.search(r'Duration:\s*(\d+):(\d+):([\d.]+)', text)
            if m:
                h, mn, s = int(m.group(1)), int(m.group(2)), float(m.group(3))
                return h * 3600 + mn * 60 + s
        except Exception as e:
            _viz_log(f"[VizEngine] _probe_audio_duration error: {e}")
        return 0.0

    def seek(self, seconds: float):
        """Seek to *seconds* into the current video playback."""
        import logging as _sk_logging
        _sk = _sk_logging.getLogger('viz_scrubber')
        if not _sk.handlers:
            import os as _sk_os
            _fh = _sk_logging.FileHandler(
                _sk_os.path.join(_sk_os.path.expanduser('~'), 'viz_scrubber_debug.log'), mode='a')
            _fh.setFormatter(_sk_logging.Formatter('%(asctime)s %(message)s'))
            _sk.addHandler(_fh)
            _sk.setLevel(_sk_logging.DEBUG)
        _sk.info(f"seek({seconds:.2f}) called, playing={self._playing}, decoder={self._video_decoder is not None}")
        if not self._playing:
            _sk.info("seek bail — not playing")
            return
        # Audio-only seek: no video decoder, just restart the audio player
        # from the requested position and re-anchor the wall clock.
        if not self._video_decoder:
            if self._audio_player and self._active_item and self._active_item.source_type == "audio":
                dur = self.get_duration()
                seconds = max(0.0, min(seconds, dur)) if dur > 0 else max(0.0, seconds)
                self._start_time = time.time() - seconds
                self._rt_last_t = seconds
                self._finished_emitted = False
                try:
                    self._audio_player.seek(seconds)
                    _sk.info(f"audio-only seek to {seconds:.3f}s done")
                except Exception as e:
                    _sk.info(f"audio-only seek error: {e}")
            else:
                _sk.info("seek bail — not playing or no decoder")
            return
        dur = self.get_duration()
        seconds = max(0.0, min(seconds, dur)) if dur > 0 else max(0.0, seconds)
        # Adjust the wall-clock start time so elapsed == seconds
        self._start_time = time.time() - seconds
        # Reset wall-clock jump guard so the seek doesn't look like a jump.
        self._rt_last_t = seconds
        # Seek the video decoder to the corresponding frame
        fps = getattr(self._video_decoder, 'fps', 30) or 30
        frame_num = int(seconds * fps)
        _sk.info(f"decoder.seek(frame={frame_num})")
        # Clear the finished flags BEFORE issuing the seek so the render
        # tick cannot race and re-stop() while the pipe is being restarted.
        self._video_decoder._finished = False
        self._finished_emitted = False
        self._video_decoder.seek(frame_num)
        _sk.info("decoder.seek done")
        # Seek audio player if available.
        # Use setPosition() only — do NOT stop/play, which on some
        # Windows media backends triggers a synchronous pipeline rebuild
        # that blocks the event loop for several seconds.
        if self._audio_player:
            try:
                _sk.info(f"audio seek to {seconds:.3f}s")
                self._audio_player.seek(seconds)
                _sk.info("audio seek done")
            except Exception as e:
                _sk.info(f"audio seek error: {e}")
        # Log next 10 render ticks after seek for diagnostics
        self._rt_log_next = 10
        _sk.info("seek complete")

    # -- Canvas management --



    def set_preview_canvas(self, canvas: VisualizerCanvas):

        self._preview_canvas = canvas



    def get_fullscreen_window(self) -> FullscreenOutputWindow | None:

        return self._fullscreen_window



    def open_fullscreen(self, screen_index: int = -1):

        """Open fullscreen output on the specified screen (or primary if -1)."""

        if self._fullscreen_window is not None:

            self._fullscreen_window.close()



        self._fullscreen_window = FullscreenOutputWindow()

        self._fullscreen_window.closed.connect(self._on_fullscreen_closed)



        screens = QApplication.screens()

        if 0 <= screen_index < len(screens):

            screen = screens[screen_index]

        elif len(screens) > 1:

            screen = screens[1]  # default to second monitor

        else:

            screen = screens[0]



        geo = screen.geometry()

        self._fullscreen_window.setGeometry(geo)

        self._fullscreen_window.showFullScreen()



    def close_fullscreen(self):

        if self._fullscreen_window:

            self._fullscreen_window.close()

            self._fullscreen_window = None



    def _on_fullscreen_closed(self):

        self._fullscreen_window = None



    # -- NDI output --



    def start_ndi(self, source_name: str = "Lighting Designer Visualizer",
                  bind_ip: str = "", compress: str = "none") -> bool:

        """Start sending frames via NDI.  Returns True if successful."""

        try:

            from .ndi_sender import NDISender, NDI_AVAILABLE

        except ImportError:

            from ndi_sender import NDISender, NDI_AVAILABLE

        if not NDI_AVAILABLE:

            return False

        self.stop_ndi()  # tear down any previous sender

        # Store config so the health-check timer can recreate the sender
        self._ndi_source_name = source_name
        self._ndi_bind_ip = bind_ip
        self._ndi_compress = compress

        self._ndi_sender = NDISender(

            source_name=source_name,

            width=self._render_width,

            height=self._render_height,

            fps=self._target_fps,

            bind_ip=bind_ip,

            compress=compress,

        )

        if self._ndi_sender.is_active:

            # Pre-create the black frame used when nothing is playing

            self._ndi_black_frame = QImage(self._render_width, self._render_height,

                                           QImage.Format.Format_ARGB32)

            self._ndi_black_frame.fill(QColor(0, 0, 0))

            # Start a keepalive timer that sends black when the render loop is idle

            if not self._render_timer.isActive():

                self._ndi_keepalive_timer.start(1000 // max(1, self._target_fps))

            # Start the health monitor (checks every 5 seconds)
            self._ndi_health_timer.start(5000)
        else:
            self._ndi_start_error = getattr(self._ndi_sender, '_init_error', '')

        return self._ndi_sender.is_active



    def stop_ndi(self):

        """Stop NDI output and release resources."""

        self._ndi_health_timer.stop()

        self._ndi_keepalive_timer.stop()

        if self._ndi_sender is not None:

            self._ndi_sender.destroy()

            self._ndi_sender = None

        self._ndi_black_frame = None



    @property

    def ndi_active(self) -> bool:

        return self._ndi_sender is not None and self._ndi_sender.is_active



    def _ndi_keepalive_tick(self):

        """Send a black frame to NDI so the receiver doesn't report 'offline'."""

        if self._ndi_sender is not None and self._ndi_sender.is_active and self._ndi_black_frame is not None:

            try:

                self._ndi_sender.send_frame(self._ndi_black_frame)

            except Exception:

                pass

    def _ndi_health_check(self):
        """Periodic check — reinitialize the NDI sender if it has become unhealthy."""
        if self._ndi_sender is None:
            return
        if getattr(self, '_shutting_down', False):
            return
        if not self._ndi_sender.is_healthy:
            _viz_log(f"[VizEngine] NDI sender unhealthy "
                     f"({self._ndi_sender._consecutive_failures} consecutive failures) "
                     f"— attempting reinitialize...")
            ok = self._ndi_sender.reinitialize()
            if ok:
                _viz_log("[VizEngine] NDI sender reinitialized successfully")
                # Re-create the black keepalive frame in case resolution changed
                self._ndi_black_frame = QImage(
                    self._render_width, self._render_height,
                    QImage.Format.Format_ARGB32)
                self._ndi_black_frame.fill(QColor(0, 0, 0))
            else:
                _viz_log("[VizEngine] NDI reinitialize failed — will retry in 5s")

    # ---- SRT output helpers ----

    def start_srt(self, port: int = 9000, mode: str = "listener",
                  target_ip: str = "", bitrate: str = "4M",
                  streamid: str = "", passphrase: str = "") -> bool:
        """Start the SRT sender.  Returns True on success."""
        self.stop_srt()
        try:
            try:
                from .srt_sender import SRTSender, SRT_AVAILABLE
            except ImportError:
                from srt_sender import SRTSender, SRT_AVAILABLE
            if not SRT_AVAILABLE:
                self._srt_start_error = "SRT unavailable (PyAV not installed)"
                _viz_log(f"[VizEngine] {self._srt_start_error}")
                return False
            sender = SRTSender(
                port=port,
                width=self._render_width,
                height=self._render_height,
                fps=self._target_fps,
                bitrate=bitrate,
                mode=mode,
                target_ip=target_ip if mode == "caller" else "",
                streamid=streamid,
                passphrase=passphrase,
            )
            sender.start()
            self._srt_sender = sender
            self._srt_black_frame = QImage(
                self._render_width, self._render_height,
                QImage.Format.Format_ARGB32)
            self._srt_black_frame.fill(QColor(0, 0, 0))
            self._srt_keepalive_timer.start()
            self._srt_start_error = ""
            _viz_log(f"[VizEngine] SRT started  mode={mode} port={port}")
            return True
        except Exception as exc:
            self._srt_start_error = str(exc)
            _viz_log(f"[VizEngine] SRT start failed: {exc}")
            return False

    def stop_srt(self):
        """Stop the SRT sender if running."""
        self._srt_keepalive_timer.stop()
        sender = self._srt_sender
        self._srt_sender = None
        if sender is not None:
            try:
                sender.stop()
            except Exception:
                pass

    @property
    def srt_active(self) -> bool:
        return self._srt_sender is not None

    def _srt_keepalive_tick(self):
        """Send a black frame when the render loop is idle so the SRT
        connection stays alive."""
        if self._srt_sender is None:
            return
        if self._render_timer.isActive():
            return  # render loop is feeding frames
        if self._srt_black_frame is not None:
            try:
                self._srt_sender.send_frame(self._srt_black_frame)
            except Exception:
                pass

    # -- Item management --



    def set_items(self, items: dict[str, VisualizerItem]):

        self._items = items



    def set_pages(self, pages: list[VisualizerPage]):

        self._pages = pages



    def get_item(self, item_id: str) -> VisualizerItem | None:

        return self._items.get(item_id)



    # -- Playback control --



    def play(self, item: VisualizerItem):

        """Start playing a visualizer item (effect or video)."""

        _viz_log(f"[VizEngine] play() called: source_type={item.source_type}, video_path='{item.video_path}', effect_type={item.effect_type}")

        # ── Effect overlay: if a song is already playing and an effect item
        # is requested, overlay it without stopping the song/audio. ──
        if (item.source_type == "effect"
                and self._song_layer_item is not None
                and self._playing):
            self._active_effect = create_effect(item.effect_type)
            self._effect_overlay_item = item
            # _active_item stays as the song so position/duration stay correct
            _viz_log(f"[VizEngine] Effect overlay started: {item.name}")
            self.effect_overlay_changed.emit(True)
            return

        self.stop()

        VisualizerEngine._tick_count = 0  # Reset diagnostic counter
        self._first_frame_logged = False  # Reset first-frame log flag

        self._active_item = item

        self._playing = True

        self._finished_emitted = False  # guard: emit playback_finished at most once per play

        # Clear stale transport / scrubber state from any prior play.
        # These are Python attributes set by the play/pause UI in the visualizer
        # tab; if left over from a previous song they confuse pause/resume
        # logic and can wedge the scrubber after an auto-advance (e.g. cue).
        self._paused = False
        self._pause_elapsed = 0.0
        self._pause_wall_time: float = 0.0
        self._pos_emit_counter = 0

        # Resolve the parent GUI window once here so all branches below can
        # reference `gui` without causing an UnboundLocalError (Python sees
        # any assignment to `gui` in the same function scope and treats the
        # name as local throughout, even before the assignment executes).
        gui = self.parent()

        # Show loading status on canvas

        if self._preview_canvas and hasattr(self._preview_canvas, 'set_status'):

            display_name = item.name or 'Unknown'

            self._preview_canvas.set_status(f"Loading: {display_name}...")



        if item.source_type == "video" and item.video_path:

            _viz_log(f"[VizEngine] Creating VideoDecoder for: {item.video_path}")

            # Decode at the current render size — the VideoDecoder will
            # scale and letterbox in OpenCV (fast C/numpy) so the frame
            # arrives at the exact output resolution every tick.
            decode_target = (self._render_width, self._render_height)

            # Use pre-transcoded MJPEG proxy if the item has one.
            # For legacy items added before the proxy system, kick off a
            # background transcode so the NEXT play is smooth — but play
            # the original source immediately so the user doesn't wait.
            import os
            video_src = item.video_path

            def _usable_proxy(p: str) -> bool:
                """True if *p* is a proxy file that looks valid (exists, >1 KB)."""
                return bool(p) and os.path.isfile(p) and os.path.getsize(p) > 1024

            if _usable_proxy(item.proxy_path):
                video_src = item.proxy_path
                _viz_log(f"[VizEngine] Using proxy: {video_src}")
            elif _usable_proxy(_proxy_cache.get(video_src, "")):
                video_src = _proxy_cache[video_src]
                _viz_log(f"[VizEngine] Using cached proxy: {video_src}")
            else:
                # No usable proxy yet — play the original immediately.
                # If a proxy is warranted, build it in the background so
                # the NEXT time this item plays it will be faster.
                if item.proxy_path and not _usable_proxy(item.proxy_path):
                    _viz_log(f"[VizEngine] Stale/invalid proxy_path cleared: {item.proxy_path}")
                    item.proxy_path = ""
                if _needs_proxy(video_src, self._render_width, self._render_height):
                    _viz_log(f"[VizEngine] Proxy needed — building in background while playing original: {video_src}")
                    self._proxy_pending_item = item
                    self._proxy_thread = threading.Thread(
                        target=_create_video_proxy,
                        args=(video_src, self._render_width, self._render_height),
                        daemon=True,
                    )
                    self._proxy_thread.start()
                    self._proxy_check_timer = QTimer(self)
                    self._proxy_check_timer.setTimerType(Qt.TimerType.CoarseTimer)
                    self._proxy_check_timer.timeout.connect(self._check_proxy_ready)
                    self._proxy_check_timer.start(250)
                    # DON'T return — fall through to create a VideoDecoder
                    # on the original source so playback starts instantly.

            self._video_decoder = VideoDecoder(video_src, loop=item.loop,
                                               target_size=decode_target)

            _viz_log(f"[VizEngine] VideoDecoder created, is_open={self._video_decoder.is_open}")

            if not self._video_decoder.is_open:

                _viz_log(f"[VizEngine] WARNING: Video decoder failed to open!")

                if self._preview_canvas and hasattr(self._preview_canvas, 'set_status'):

                    self._preview_canvas.set_status(f"ERROR: Cannot open video\n{item.video_path}")

                self._video_decoder = None

            else:

                if self._preview_canvas and hasattr(self._preview_canvas, 'clear_status'):

                    self._preview_canvas.clear_status()

                # Prepare audio track (uses QMediaPlayer for the same

                # video file — decodes audio independently of OpenCV).

                # We defer .play() until just before the render timer starts

                # so audio and video kick off at the same instant.

                try:
                    self._audio_player = _VideoAudioPlayer(item.video_path, loop=item.loop)
                except Exception as e:
                    _viz_log(f"[VizEngine] Audio player error: {e}")
                    self._audio_player = None

                # Apply the current video-volume slider level so a new
                # video respects the user's volume setting immediately.
                if self._audio_player and gui and hasattr(gui, '_apply_visualizer_audio_volume'):
                    gui._apply_visualizer_audio_volume()

                # Start NDI audio extraction in the background if enabled
                if self._ndi_audio_enabled and self.ndi_active:
                    try:
                        self._ndi_audio_extractor = _NDIAudioExtractor(item.video_path)
                    except Exception as e:
                        _viz_log(f"[VizEngine] NDI audio extractor error: {e}")
                        self._ndi_audio_extractor = None

        elif item.source_type == "ndi_input":
            # Live NDI input — connect to a network source
            try:
                from .ndi_receiver import NDIReceiver, NDISource
            except ImportError:
                from ndi_receiver import NDIReceiver, NDISource
            ndi_src = NDISource(
                name=getattr(item, '_ndi_source_obj_name', item.name),
                url=getattr(item, '_ndi_source_obj_url', ''),
            )
            self._ndi_receiver = NDIReceiver(ndi_src)
            if self._ndi_receiver.start():
                if self._preview_canvas and hasattr(self._preview_canvas, 'clear_status'):
                    self._preview_canvas.clear_status()
            else:
                if self._preview_canvas and hasattr(self._preview_canvas, 'set_status'):
                    self._preview_canvas.set_status(f"ERROR: Cannot connect to NDI source\n{item.name}")
                self._ndi_receiver = None

        elif item.source_type == "usb_capture":
            # Local USB/HDMI capture card
            try:
                from .ndi_receiver import USBCaptureReceiver, USBCaptureDevice
            except ImportError:
                from ndi_receiver import USBCaptureReceiver, USBCaptureDevice
            dev = USBCaptureDevice(
                index=getattr(item, '_usb_device_index', 0),
                name=getattr(item, '_usb_device_name', item.name),
            )
            self._usb_receiver = USBCaptureReceiver(dev)
            if self._usb_receiver.start():
                if self._preview_canvas and hasattr(self._preview_canvas, 'clear_status'):
                    self._preview_canvas.clear_status()
            else:
                if self._preview_canvas and hasattr(self._preview_canvas, 'set_status'):
                    self._preview_canvas.set_status(f"ERROR: Cannot open capture device\n{item.name}")
                self._usb_receiver = None

        elif item.source_type == "effect":

            self._active_effect = create_effect(item.effect_type)

            if self._preview_canvas and hasattr(self._preview_canvas, 'clear_status'):

                self._preview_canvas.clear_status()

        elif item.source_type == "audio" and item.video_path:
            # Audio-only item — no video decoder, just the audio player
            try:
                self._audio_player = _VideoAudioPlayer(item.video_path, loop=item.loop)
            except Exception as e:
                _viz_log(f"[VizEngine] Audio player error: {e}")
                self._audio_player = None
            if self._audio_player and gui and hasattr(gui, '_apply_visualizer_audio_volume'):
                gui._apply_visualizer_audio_volume()
            # Probe duration so the scrubber has a range to work with.
            # Run in a background thread so the main thread isn't blocked.
            import threading as _threading
            def _probe_and_store(path=item.video_path):
                dur = VisualizerEngine._probe_audio_duration(path)
                self._audio_duration = dur
                _viz_log(f"[VizEngine] Audio duration probed: {dur:.2f}s")
            _threading.Thread(target=_probe_and_store, daemon=True,
                              name="viz-audio-probe").start()
            if self._preview_canvas and hasattr(self._preview_canvas, 'set_status'):
                self._preview_canvas.set_status(f"🎵 {item.name}")

        else:

            _viz_log(f"[VizEngine] WARNING: No decoder/effect created. source_type={item.source_type}, video_path='{item.video_path}'")

            if self._preview_canvas and hasattr(self._preview_canvas, 'set_status'):

                self._preview_canvas.set_status(f"Nothing to play for: {item.name}")



        # Match the video's native FPS (capped at 30) for smooth playback.
        # Effects still get the full configured frame rate.
        playback_fps = self._target_fps
        if item.source_type == "video" and self._video_decoder:
            playback_fps = min(max(int(self._video_decoder.fps), 24), self._target_fps, 30)
        interval = 1000 // playback_fps

        # Start audio and video at the same instant so they stay in sync.

        self._start_time = time.time()
        # Reset the wall-clock-jump guard so a fresh play doesn't trigger
        # re-anchoring on the very first tick.
        self._rt_last_t = None

        # Reset NDI frame counter for clean timecodes

        if self._ndi_sender is not None:

            self._ndi_sender._frame_count = 0

        if self._audio_player:

            try:

                self._audio_player.play()

            except Exception as e:

                _viz_log(f"[VizEngine] Audio player play() error: {e}")

        self._render_timer.start(interval)

        # Apply trim_start: seek past leading silence/dead air.
        # Use singleShot so the decoder/audio thread has started before we seek.
        trim_s = getattr(item, 'trim_start', 0.0) or 0.0
        if trim_s > 0:
            QTimer.singleShot(80, lambda ts=trim_s: self.seek(ts) if self._playing else None)

        # Suppress Python GC gen-2 collections during playback —
        # they cause 5-50 ms stalls every few seconds.
        import gc as _gc
        self._gc_was_enabled = _gc.isenabled()
        _gc.disable()

        # Render loop is running — pause NDI keepalive (render loop sends frames)

        self._ndi_keepalive_timer.stop()

        canvas_info = "None"

        if self._preview_canvas:

            canvas_info = f"visible={self._preview_canvas.isVisible()}, size={self._preview_canvas.width()}x{self._preview_canvas.height()}"

        # Track this as the current song layer (cleared when stop() is called)
        if item.source_type in ("video", "audio"):
            self._song_layer_item = item
        self._effect_overlay_item = None

        _viz_log(f"[VizEngine] Timer started at {self._target_fps}fps (interval={interval}ms), "

                 f"decoder={self._video_decoder is not None}, effect={self._active_effect is not None}, "

                 f"canvas=[{canvas_info}]")



    def _check_proxy_ready(self):
        """Poll the background proxy thread; stamp proxy on item when done.

        The original video is already playing — we just record the proxy
        path for the *next* time this item is played.
        """
        if self._proxy_thread is None or self._proxy_thread.is_alive():
            return  # still running

        # Transcode finished — clean up polling timer
        if self._proxy_check_timer:
            self._proxy_check_timer.stop()
            self._proxy_check_timer.deleteLater()
            self._proxy_check_timer = None
        self._proxy_thread = None

        item = self._proxy_pending_item
        self._proxy_pending_item = None
        if item is None:
            return

        # Stamp the proxy_path on the item so it persists in the project
        if item.video_path in _proxy_cache:
            import os
            proxy = _proxy_cache[item.video_path]
            if os.path.isfile(proxy) and os.path.getsize(proxy) > 1024:
                item.proxy_path = proxy
                _viz_log(f"[VizEngine] Background proxy ready for next play: {proxy}")

    def clear_effect(self) -> None:
        """Stop the effect overlay and return to displaying the song."""
        if self._effect_overlay_item is None:
            return
        _viz_log(f"[VizEngine] Effect overlay cleared")
        self._active_effect = None
        self._effect_overlay_item = None
        # _active_item is still the song — no change needed
        self.effect_overlay_changed.emit(False)

    @property
    def effect_overlay_item(self) -> 'VisualizerItem | None':
        return self._effect_overlay_item

    def pause_playback(self):
        """Pause rendering — stops DMX/effect output; lights hold last value."""
        if not self._paused:
            self._paused = True
            self._pause_wall_time = time.time()
            if self._audio_player:
                self._audio_player.pause()

    def resume_playback(self):
        """Resume rendering from the paused position."""
        if self._paused:
            elapsed_pause = time.time() - self._pause_wall_time
            self._start_time += elapsed_pause  # re-anchor so effect/video continues from same point
            self._pause_wall_time = 0.0
            self._paused = False
            if self._audio_player:
                self._audio_player.resume()

    def stop(self):

        """Stop current playback."""

        self._render_timer.stop()

        # Re-enable GC and run a collection now that we're idle
        import gc as _gc
        if getattr(self, '_gc_was_enabled', True):
            _gc.enable()
        _gc.collect()

        self._playing = False

        self._active_item = None

        # Clear overlay state
        had_overlay = self._effect_overlay_item is not None
        self._song_layer_item = None
        self._effect_overlay_item = None
        if had_overlay:
            self.effect_overlay_changed.emit(False)

        # Reset the playback clock so any consumer that polls _start_time
        # (e.g. the Video Timecode source) never reports a phantom "running"
        # state after stop()/on next launch.
        self._start_time = 0.0

        # Cancel any in-progress proxy transcoding poll
        if self._proxy_check_timer:
            self._proxy_check_timer.stop()
            self._proxy_check_timer.deleteLater()
            self._proxy_check_timer = None
        self._proxy_pending_item = None
        # (The daemon thread will finish on its own; no need to join.)
        self._proxy_thread = None

        # If NDI is active, start the keepalive timer so the stream stays live
        # (skip during shutdown — NDI sender is about to be destroyed)

        if (self._ndi_sender is not None and self._ndi_sender.is_active
                and not getattr(self, '_shutting_down', False)):

            self._ndi_keepalive_timer.start(1000 // max(1, self._target_fps))



        if self._audio_player:

            self._audio_player.release()

            self._audio_player = None

        if self._ndi_audio_extractor:
            self._ndi_audio_extractor.release()
            self._ndi_audio_extractor = None

        if self._ndi_receiver:
            self._ndi_receiver.stop()
            self._ndi_receiver = None

        if self._usb_receiver:
            self._usb_receiver.stop()
            self._usb_receiver = None

        if self._video_decoder:

            self._video_decoder.release()

            self._video_decoder = None

        self._audio_duration = 0.0
        self._active_effect = None

        # Zero out any DMX channels the spatial mapper was driving
        self.spatial_mapper.zero_channels()

        # Clear canvases to black

        black = QImage(self._render_width, self._render_height, QImage.Format.Format_RGB32)

        black.fill(QColor(0, 0, 0))

        self._distribute_frame(black)



    _tick_count = 0  # class-level debug counter

    def _render_tick(self):

        """Called by timer — render one frame and distribute it."""

        if not self._playing:

            return

        if self._paused:
            return

        # Re-entrancy guard: if a previous tick is still executing (e.g.
        # because the event loop processed a queued timer fire while we
        # were inside paintEvent or a signal handler), bail out immediately
        # to prevent frame pile-up that freezes the GUI.
        if getattr(self, '_in_render_tick', False):
            return
        self._in_render_tick = True
        # Diagnostic: log render ticks and detect long-running ticks
        _rt_counter = getattr(self, '_rt_diag_counter', 0) + 1
        self._rt_diag_counter = _rt_counter
        _log_next = getattr(self, '_rt_log_next', 0)
        import logging as _rtl
        _rtlog = _rtl.getLogger('viz_scrubber')
        if _rt_counter % 30 == 0 or _log_next > 0:
            _rtlog.info(f"render_tick #{_rt_counter} (log_next={_log_next})")
            if _log_next > 0:
                self._rt_log_next = _log_next - 1
        _t0 = time.perf_counter()
        try:
            self._do_render_tick(_rt_counter)
        except Exception as _rte:
            _rtlog.info(f"render_tick EXCEPTION: {_rte}")
        finally:
            _elapsed_ms = (time.perf_counter() - _t0) * 1000.0
            if _elapsed_ms > 80:
                _rtlog.warning(
                    f"render_tick #{_rt_counter} SLOW: {_elapsed_ms:.0f}ms")
            self._in_render_tick = False

    def _do_render_tick(self, _rt_counter: int = 0):
        """Actual render work — separated so _render_tick can guard re-entrancy."""
        import logging as _dtl
        _dtlog = _dtl.getLogger('viz_scrubber')
        _log_this = getattr(self, '_rt_log_next', 0) > 0
        _N = _rt_counter
        frame = None

        t = time.time() - self._start_time

        # ── Wall-clock jump guard ────────────────────────────────────────
        # Render ticks fire roughly every 1/_target_fps seconds. If ``t``
        # leaps forward by several seconds between ticks, the system clock
        # was almost certainly adjusted (NTP correction, time-zone change,
        # or — most commonly — return from sleep/hibernate). Without this
        # guard the elapsed-time math would push the decoder past EOF and
        # spuriously fire ``playback_finished``, which in continuous mode
        # silently skips to the next song. Re-anchor ``_start_time`` so the
        # apparent elapsed time advances by a single normal frame instead.
        try:
            _last_t = getattr(self, '_rt_last_t', None)
            if _last_t is not None and (t - _last_t) > 5.0:
                _jump = t - _last_t
                _frame_step = 1.0 / max(1, self._target_fps)
                self._start_time += (_jump - _frame_step)
                t = time.time() - self._start_time
                _viz_log(
                    f"[VizEngine] Wall-clock jump detected (+{_jump:.1f}s) "
                    f"— re-anchored start_time; new elapsed={t:.2f}s"
                )
            self._rt_last_t = t
        except Exception:
            pass

        # Emit position for scrubber (throttled to ~4 Hz to avoid UI overhead)
        _pos_counter = getattr(self, '_pos_emit_counter', 0) + 1
        self._pos_emit_counter = _pos_counter
        if _pos_counter % max(1, self._target_fps // 4) == 0:
            dur = self.get_duration()
            if dur > 0:
                # When video is looping (repeat mode), wrap position so TC
                # resets to 0 at the start of each loop instead of counting up
                pos = t
                if self._active_item and getattr(self._active_item, 'loop', False) and dur > 0:
                    pos = t % dur
                self.position_changed.emit(pos, dur)



        if self._ndi_receiver is not None:
            frame = self._ndi_receiver.latest_frame()
            # NDI input is a live stream — never "finishes"

        elif self._usb_receiver is not None:
            frame = self._usb_receiver.latest_frame()
            # USB/HDMI capture is a live stream — never "finishes"

        elif self._video_decoder:
            if _log_this:
                _dtlog.info(f"  pre-read: is_open={self._video_decoder.is_open}, finished={self._video_decoder.finished}, seek_req={getattr(self._video_decoder, '_seek_request', -1)}, elapsed={t:.2f}")

            if self._video_decoder.is_open:
                try:
                    if _log_this:
                        _dtlog.info("  calling read_frame...")
                    frame = self._video_decoder.read_frame(elapsed=t)
                    if _log_this:
                        _dtlog.info(f"  read_frame returned {'OK' if frame else 'None'}")
                except Exception as e:
                    if VisualizerEngine._tick_count < 3:
                        _viz_log(f"[VizEngine] read_frame exception: {e}")
                    frame = None
            else:
                if _log_this:
                    _dtlog.info("  decoder not open, draining queue")
                # Pipe closed (EOF) but the decode queue may still have
                # buffered frames.  Drain the queue so the last second of
                # video is actually shown before we fire playback_finished.
                with self._video_decoder._queue_lock:
                    if self._video_decoder._frame_queue:
                        _, frame = self._video_decoder._frame_queue.popleft()
                        if frame is not None:
                            self._video_decoder._last_delivered = frame

            if VisualizerEngine._tick_count < 3 or (frame is not None and not getattr(self, '_first_frame_logged', False)):
                if frame is not None and not getattr(self, '_first_frame_logged', False):
                    self._first_frame_logged = True
                    _viz_log(f"[VizEngine] FIRST VIDEO FRAME at tick #{VisualizerEngine._tick_count}, t={t:.2f}s, size={frame.width()}x{frame.height()}")

                VisualizerEngine._tick_count += 1

                _viz_log(f"[VizEngine] _render_tick #{VisualizerEngine._tick_count}: video frame={'OK' if frame is not None else 'None'}, finished={self._video_decoder.finished}, canvas={self._preview_canvas is not None}")

            # Check finished OUTSIDE the is_open guard — the ffmpeg
            # subprocess sets _opened=False on EOF, so is_open becomes
            # False before we can detect the finished state.
            #
            # Also treat is_open=False + non-looping as finished even if
            # the decode thread hasn't flagged _finished yet — the pipe
            # is gone, so we'll never get another frame.
            #
            # IMPORTANT: Do NOT mark as finished while a seek request is
            # pending.  During a seek the background decode thread kills
            # the old ffmpeg pipe and starts a new one; there is a brief
            # window where is_open is False even though playback should
            # continue.  _seek_request >= 0 or _read_pos having just been
            # reset indicates that a seek is in progress.
            decoder_done = self._video_decoder.finished
            seek_in_progress = (getattr(self._video_decoder, '_seek_request', -1) >= 0
                                or getattr(self._video_decoder, '_seeking_active', False))
            if _log_this:
                _dtlog.info(f"  finished check: decoder_done={decoder_done}, is_open={self._video_decoder.is_open}, seek_in_progress={seek_in_progress}, loop={getattr(self._active_item, 'loop', '?')}")
            if not decoder_done and not self._video_decoder.is_open and not seek_in_progress:
                if self._active_item and not self._active_item.loop:
                    if _log_this:
                        _dtlog.info("  >>> MARKING AS FINISHED <<<")
                    self._video_decoder._finished = True
                    decoder_done = True
                    _viz_log(f"[VizEngine] decoder_done=True (pipe closed): t={t:.2f}s, is_open={self._video_decoder.is_open}, vd_finished={self._video_decoder.finished}, seek_in_progress={seek_in_progress}, read_pos={getattr(self._video_decoder,'_read_pos',None)}")

            # trim_end: stop early before the video's natural end.
            if (self._active_item and not self._active_item.loop
                    and not getattr(self, '_finished_emitted', False)
                    and not seek_in_progress):
                _trim_end_v = getattr(self._active_item, 'trim_end', 0.0) or 0.0
                if _trim_end_v > 0 and t >= _trim_end_v:
                    self._finished_emitted = True
                    _fid = self._active_item.id
                    _viz_log(f"[VizEngine] Video trim_end reached at {t:.2f}s — finishing")
                    self.stop()
                    QTimer.singleShot(0, lambda fid=_fid: self.playback_finished.emit(fid))
                    return

            if frame is None and decoder_done:

                if self._active_item and not self._active_item.loop and not getattr(self, '_finished_emitted', False):
                    if _log_this:
                        _dtlog.info("  >>> STOPPING PLAYBACK (finished) <<<")

                    self._finished_emitted = True
                    finished_id = self._active_item.id
                    _viz_log(f"[VizEngine] Video finished — emitting playback_finished for {finished_id}")

                    self.stop()

                    # Defer the signal to the next event-loop iteration so
                    # the handler (which may call play() for the next video)
                    # runs OUTSIDE the current render tick's stack frame.
                    # This avoids re-entrancy issues with stop→play nesting.
                    QTimer.singleShot(0, lambda fid=finished_id: self.playback_finished.emit(fid))

                    return

            # Only render an effect overlay if one is actually active.
            # Without this guard, _render_effect() returns a black QImage
            # (because _active_effect is None) and overwrites the decoded
            # video frame, making the canvas permanently black.
            if self._active_effect is not None:
                try:
                    effect_overlay = self._render_effect(t)
                    if effect_overlay is not None:
                        frame = effect_overlay
                except Exception as _eff_err:
                    import traceback as _tb
                    if VisualizerEngine._tick_count < 5:
                        print(f"[VizEngine] Effect render error: {_eff_err}")
                        _tb.print_exc()

        elif self._active_effect and self._active_item:

            # Pure generated-effect item (no video decoder) — render the
            # effect as the full frame.
            try:
                frame = self._render_effect(t)
            except Exception as _eff_err:
                import traceback as _tb
                if VisualizerEngine._tick_count < 5:
                    print(f"[VizEngine] Effect render error: {_eff_err}")
                    _tb.print_exc()
                frame = None

        else:

            # Nothing to render — log once (suppress for audio-only items)
            is_audio = self._active_item and self._active_item.source_type == "audio"

            if is_audio:
                # For audio-only items: update scrubber and detect end-of-track.
                dur = self.get_duration()
                if dur > 0:
                    _pos_counter = getattr(self, '_pos_emit_counter', 0) + 1
                    self._pos_emit_counter = _pos_counter
                    if _pos_counter % max(1, self._target_fps // 4) == 0:
                        pos = min(t, dur)
                        self.position_changed.emit(pos, dur)
                    # Detect end of audio (elapsed >= duration) and not looping
                    loop = self._active_item and getattr(self._active_item, 'loop', False)
                    # dur already respects trim_end via get_duration()
                    if t >= dur and not loop and not getattr(self, '_finished_emitted', False):
                        self._finished_emitted = True
                        finished_id = self._active_item.id
                        _viz_log(f"[VizEngine] Audio finished — emitting playback_finished for {finished_id}")
                        self.stop()
                        QTimer.singleShot(0, lambda fid=finished_id: self.playback_finished.emit(fid))
                        return

            elif VisualizerEngine._tick_count < 1:

                VisualizerEngine._tick_count = 1

                _viz_log(f"[VizEngine] _render_tick: no decoder and no effect! decoder={self._video_decoder}, effect={self._active_effect}")



        if frame is not None:

            # Normally the VideoDecoder already delivers frames at the
            # exact render size.  This fallback handles generated effects
            # or edge cases where the size still differs.
            rw, rh = self._render_width, self._render_height
            if frame.width() != rw or frame.height() != rh:
                frame = frame.scaled(
                    rw, rh,
                    Qt.AspectRatioMode.IgnoreAspectRatio,
                    Qt.TransformationMode.FastTransformation,
                )

            self._last_frame = frame  # keep for thumbnail capture (undimmed)

            # DMX spatial mapping — feed the UNDIMMED frame so fixtures
            # receive accurate colours; the fixture's own dimmer channel
            # handles brightness via the master fader separately.
            # (To revert: move this block below _apply_brightness and
            #  change self._last_frame → frame)
            if self.spatial_mapper.enabled:
                self.spatial_mapper.map_frame(self._last_frame)

            # Apply fader-level brightness scaling if below 1.0
            fl = self._fader_level
            if fl < 1.0:
                frame = self._apply_brightness(frame, fl)

            self._distribute_frame(frame)

            # Send NDI audio chunk for this frame's time window
            if (self._ndi_audio_extractor and self._ndi_sender
                    and self._ndi_sender.is_active):
                loop = self._active_item.loop if self._active_item else False
                frame_dur = 1.0 / max(1, self._target_fps)
                planar, n_samples = self._ndi_audio_extractor.read_chunk(
                    t, frame_dur, loop=loop
                )
                if planar and n_samples > 0:
                    self._ndi_sender.send_audio(
                        planar,
                        _NDIAudioExtractor.NDI_SAMPLE_RATE,
                        _NDIAudioExtractor.NDI_CHANNELS,
                        n_samples,
                    )



    # Safety cap for CPU rendering on very high-resolution outputs (4K+).
    # At 1080p and below the CPU renders at native resolution.
    _EFFECT_CPU_MAX_W = 1920
    _EFFECT_CPU_MAX_H = 1080

    def _render_effect(self, t: float) -> QImage:

        """Render the active generated effect to a QImage.

        Tries the GPU-accelerated FBO path first when enabled.  Otherwise
        renders on the CPU at native resolution (capped at 1080p to protect
        against 4K output melting the CPU).
        """

        ow, oh = self._render_width, self._render_height
        # When an effect overlay is active (effect on top of a playing song),
        # _active_item is the song (video) which has effect_params=None.
        # Use the overlay item's params so the effect renders correctly.
        _effect_source = self._effect_overlay_item if self._effect_overlay_item is not None else self._active_item
        raw_params = _effect_source.effect_params if _effect_source is not None else None
        params = raw_params if raw_params is not None else VisualEffectParams()

        # Inject fixture positions so fixture-aware effects can use them
        try:
            fxs = self.spatial_mapper._fixtures or self._project_fixtures
            if fxs:
                params.fixture_positions = []
                for f in fxs:
                    prof = f.profile if hasattr(f, 'profile') else None
                    p_rows = getattr(prof, 'pixel_rows', 1) if prof else 1
                    p_cols = getattr(prof, 'pixel_columns', 1) if prof else 1
                    # A fixture is pixel-mapped when it says so OR if the
                    # profile defines a multi-cell grid (rows*cols > 1).
                    is_px = (getattr(f, 'is_pixel_mapped', False)
                             or getattr(prof, 'is_pixel_fixture', False)
                             or (p_rows * p_cols) > 1)
                    entry = {
                        'x': getattr(f, 'location_x', 0.5),
                        'y': getattr(f, 'location_y', 0.5),
                        'label': getattr(f, 'label', ''),
                        'id': getattr(f, 'id', ''),
                        'w': getattr(f, 'visual_width', 0.1),
                        'h': getattr(f, 'visual_height', 0.05),
                        'is_pixel': is_px,
                        'pixel_rows': p_rows,
                        'pixel_cols': p_cols,
                        'rotation': getattr(f, 'fixture_rotation', 0),
                        'category': getattr(prof, 'category', '') if prof else '',
                    }
                    params.fixture_positions.append(entry)
            else:
                params.fixture_positions = []
        except Exception:
            params.fixture_positions = []

        # ---- GPU FBO path (opt-in) ----
        if self._gpu_renderer is not None:
            img = self._gpu_renderer.render(
                self._active_effect, ow, oh, t, params
            )
            if img is not None:
                return img
            # GPU render returned None — disable and fall through to CPU
            _viz_log("[VizEngine] GPU render failed, falling back to CPU")
            self._gpu_renderer = None

        # ---- CPU path (native resolution, capped at 1080p) ----
        if ow > self._EFFECT_CPU_MAX_W or oh > self._EFFECT_CPU_MAX_H:
            scale = min(self._EFFECT_CPU_MAX_W / ow, self._EFFECT_CPU_MAX_H / oh)
            ew = max(64, int(ow * scale))
            eh = max(36, int(oh * scale))
        else:
            ew, eh = ow, oh

        img = QImage(ew, eh, QImage.Format.Format_RGB32)

        img.fill(QColor(0, 0, 0))

        painter = QPainter(img)

        painter.setRenderHint(QPainter.RenderHint.Antialiasing)

        # Apply global zoom via QPainter transform so ALL effects respond
        # to the scale / zoom slider, not just those that read params.scale.
        zoom = getattr(params, 'scale', 1.0)
        if zoom != 1.0:
            cx, cy = ew / 2.0, eh / 2.0
            painter.translate(cx, cy)
            painter.scale(zoom, zoom)
            painter.translate(-cx, -cy)

        try:
            self._active_effect.render(painter, ew, eh, t, params)
        except Exception as _eff_err:
            import traceback as _tb
            if not hasattr(self, '_eff_err_count'):
                self._eff_err_count = 0
            self._eff_err_count += 1
            if self._eff_err_count <= 3:
                print(f"[VizEngine] Effect render error #{self._eff_err_count}: {_eff_err}")
                _tb.print_exc()

        # Beat diagnostics removed from render loop (caused 10-50ms stalls every ~5s)

        # --- Silence-fade overlay (fades to black after ~3 s of no audio) ---
        if getattr(params, 'silence_fade', False):
            try:
                from .visualizer_effects import MicBeatDetector
            except ImportError:
                from visualizer_effects import MicBeatDetector
            bd = MicBeatDetector.get()
            energy = bd.energy
            # Track last-heard time on the engine (lightweight)
            if not hasattr(self, '_sf_last_sound'):
                self._sf_last_sound = time.monotonic()
            now = time.monotonic()
            if energy > 0.02:
                self._sf_last_sound = now
            silence_dur = now - self._sf_last_sound
            if silence_dur > 3.0:
                # Fade from 0→1 over 2 seconds of continued silence
                fade_alpha = min(1.0, (silence_dur - 3.0) / 2.0)
                overlay_alpha = int(fade_alpha * 255)
                painter.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)
                painter.fillRect(0, 0, ew, eh, QColor(0, 0, 0, overlay_alpha))

        painter.end()

        # Scale up to actual output size if we rendered smaller
        if ew != ow or eh != oh:
            img = img.scaled(ow, oh,
                             Qt.AspectRatioMode.IgnoreAspectRatio,
                             Qt.TransformationMode.SmoothTransformation)

        return img



    # Cache sip module at class level to avoid per-frame import overhead
    _sip_mod = None
    _sip_resolved = False

    @classmethod
    def _get_sip(cls):
        if not cls._sip_resolved:
            try:
                import sip
                cls._sip_mod = sip
            except ImportError:
                try:
                    from PyQt6 import sip
                    cls._sip_mod = sip
                except ImportError:
                    cls._sip_mod = None
            cls._sip_resolved = True
        return cls._sip_mod

    def _distribute_frame(self, frame: QImage):

        """Send the rendered frame to all canvases."""

        sip = self._get_sip()



        if self._preview_canvas:

            if sip is not None and sip.isdeleted(self._preview_canvas):

                self._preview_canvas = None

            else:

                try:

                    self._preview_canvas.set_frame(frame)

                except RuntimeError:

                    self._preview_canvas = None



        # Auto-reconnect canvas from gui if lost

        if self._preview_canvas is None and self.parent() is not None:

            gui = self.parent()

            canvas = getattr(gui, '_viz_canvas', None)

            if canvas is not None:

                try:

                    if sip is not None and sip.isdeleted(canvas):

                        canvas = None

                except Exception:

                    canvas = None

                if canvas is not None:

                    self._preview_canvas = canvas

                    try:

                        self._preview_canvas.set_frame(frame)

                    except RuntimeError:

                        self._preview_canvas = None



        if self._fullscreen_window:

            if sip is not None and sip.isdeleted(self._fullscreen_window):

                self._fullscreen_window = None

            else:

                try:

                    self._fullscreen_window.set_frame(frame)

                except RuntimeError:

                    self._fullscreen_window = None

        # NDI output
        if self._ndi_sender is not None and self._ndi_sender.is_active:
            try:
                self._ndi_sender.send_frame(frame)
            except Exception as exc:
                # Failure counting is handled inside send_frame;
                # health timer will trigger reconnect if consecutive
                # failures exceed the threshold.
                if getattr(self, '_ndi_send_err_logged', 0) < 3:
                    self._ndi_send_err_logged = getattr(self, '_ndi_send_err_logged', 0) + 1
                    print(f"[VisualizerEngine] NDI send_frame error: {exc}")

        # SRT output
        if self._srt_sender is not None:
            try:
                self._srt_sender.send_frame(frame)
            except Exception as exc:
                if getattr(self, '_srt_send_err_logged', 0) < 3:
                    self._srt_send_err_logged = getattr(self, '_srt_send_err_logged', 0) + 1
                    print(f"[VisualizerEngine] SRT send_frame error: {exc}")

        self.frame_ready.emit(frame)

    # -- Brightness scaling for fader control --

    @staticmethod
    def _apply_brightness(frame: QImage, level: float) -> QImage:
        """Return a dimmed version of *frame* at *level* brightness (0.0–1.0).

        Uses a QPainter semi-transparent black overlay which avoids
        per-pixel rounding errors that cause colour banding / noise
        at low brightness levels.
        """
        if level >= 1.0:
            return frame
        if level <= 0.0:
            black = QImage(frame.size(), QImage.Format.Format_RGB32)
            black.fill(QColor(0, 0, 0))
            return black

        out = frame.copy()
        painter = QPainter(out)
        painter.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)
        alpha = int((1.0 - level) * 255)
        painter.fillRect(0, 0, out.width(), out.height(), QColor(0, 0, 0, alpha))
        painter.end()
        return out

    # -- DMX mapping configuration --



    def configure_dmx_mapping(self, fixtures: list, artnet_output):

        """Set up spatial DMX mapping with project fixtures and Art-Net output."""

        self.spatial_mapper.configure(fixtures, artnet_output)



    def set_dmx_mapping_enabled(self, enabled: bool):

        """Enable or disable DMX mapping from visualizer to fixtures."""

        self.spatial_mapper.enabled = enabled

    def set_project_fixtures(self, fixtures: list):
        """Store project fixtures so effects can read positions."""
        self._project_fixtures = list(fixtures) if fixtures else []



    # -- Cleanup --



    def shutdown(self):

        """Clean up resources."""

        self._shutting_down = True

        self.stop()

        self.stop_ndi()

        self.stop_srt()

        self.close_fullscreen()

        # Release GPU resources
        if self._gpu_renderer is not None:
            self._gpu_renderer.destroy()
            self._gpu_renderer = None

