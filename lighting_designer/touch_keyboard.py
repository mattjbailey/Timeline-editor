"""Compact virtual on-screen keyboard for touch-screen usage.

Tap (or click) into any editable text field to summon the keyboard next to
it — the field's current value is selected so the first key you type replaces
it.  Triple-tap anywhere and the F10 key also work as fallbacks.  The keyboard
inserts text into whatever text-input widget currently has focus and always
stays on top of all other windows.
"""

from __future__ import annotations

import sys
import time
import traceback

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QApplication, QLineEdit,
    QSpinBox, QDoubleSpinBox, QSizePolicy, QAbstractSpinBox, QComboBox,
    QTextEdit, QPlainTextEdit,
)
from PyQt6.QtCore import Qt, QTimer, QEvent, QPoint, QObject
from PyQt6.QtGui import QFont, QCursor, QShortcut, QKeySequence

_DBG = True  # flip to False once confirmed working


def _log(msg: str):
    if _DBG:
        try:
            print(f"[TouchKB] {msg}", file=sys.stderr, flush=True)
        except Exception:
            pass


# ───────────────────────────────────────────────────────────────────
#  Keyboard widget
# ───────────────────────────────────────────────────────────────────

_ROWS_LOWER = [
    ["1", "2", "3", "4", "5", "6", "7", "8", "9", "0"],
    ["q", "w", "e", "r", "t", "y", "u", "i", "o", "p"],
    ["a", "s", "d", "f", "g", "h", "j", "k", "l"],
    ["⇧", "z", "x", "c", "v", "b", "n", "m", "⌫"],
    ["123", "Space", ".", "Enter", "⌨"],
]

_ROWS_UPPER = [
    ["!", "@", "#", "$", "%", "^", "&", "*", "(", ")"],
    ["Q", "W", "E", "R", "T", "Y", "U", "I", "O", "P"],
    ["A", "S", "D", "F", "G", "H", "J", "K", "L"],
    ["⇧", "Z", "X", "C", "V", "B", "N", "M", "⌫"],
    ["123", "Space", ".", "Enter", "⌨"],
]

_ROWS_SYMBOL = [
    ["1", "2", "3", "4", "5", "6", "7", "8", "9", "0"],
    ["-", "/", ":", ";", "(", ")", "$", "&", "@", '"'],
    [".", ",", "?", "!", "'", "\\", "|", "~", "`"],
    ["ABC", "#", "=", "+", "_", "[", "]", "{", "⌫"],
    ["ABC", "Space", ".", "Enter", "⌨"],
]


class TouchKeyboard(QWidget):
    """Floating compact virtual keyboard – always stays on top."""

    _instance: TouchKeyboard | None = None

    @classmethod
    def instance(cls, parent=None):
        """Return the singleton keyboard, creating it lazily."""
        if cls._instance is None:
            cls._instance = cls(parent)
        return cls._instance

    def __init__(self, parent=None):
        flags = (Qt.WindowType.Window
                 | Qt.WindowType.FramelessWindowHint
                 | Qt.WindowType.WindowStaysOnTopHint
                 | Qt.WindowType.WindowDoesNotAcceptFocus)
        super().__init__(parent, flags)
        self.setAttribute(Qt.WidgetAttribute.WA_ShowWithoutActivating, True)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, False)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self._target_widget = None
        self._watched_window = None
        self._shifted = False
        self._symbols = False
        self._setup_ui()

    # ── Build ──────────────────────────────────────────────────────

    def _setup_ui(self):
        self.setStyleSheet("""
            TouchKeyboard {
                background-color: #1a1a1a;
                border: 1px solid #555;
                border-radius: 6px;
            }
        """)
        self._outer = QVBoxLayout(self)
        self._outer.setContentsMargins(8, 8, 8, 8)
        self._outer.setSpacing(4)
        self._buttons: list[list[QPushButton]] = []   # [row][col] → button
        self._current_layout = _ROWS_LOWER
        self._build_rows(_ROWS_LOWER)

    def _clear_rows(self):
        self._buttons.clear()
        while self._outer.count():
            child = self._outer.takeAt(0)
            if child.widget():
                child.widget().deleteLater()
            elif child.layout():
                while child.layout().count():
                    sub = child.layout().takeAt(0)
                    if sub.widget():
                        sub.widget().deleteLater()

    def _relabel(self, rows):
        """Fast path: update button labels without rebuilding widgets."""
        for r, row_keys in enumerate(rows):
            if r >= len(self._buttons):
                break
            for c, key in enumerate(row_keys):
                if c < len(self._buttons[r]):
                    try:
                        self._buttons[r][c].setText(key)
                    except RuntimeError:
                        # Button C++ object already deleted — rebuild instead
                        self._build_rows(rows)
                        return
        self._current_layout = rows

    def _build_rows(self, rows):
        self._clear_rows()
        self._current_layout = rows
        btn_h = 56
        btn_font = QFont("Segoe UI", 16)
        btn_style = """
            QPushButton {{
                background-color: {bg};
                color: #ffffff;
                border: 1px solid #444;
                border-radius: 6px;
                min-height: {h}px;
                max-height: {h}px;
                font-size: 18px;
                padding: 0 4px;
            }}
            QPushButton:pressed {{
                background-color: #c97a50;
            }}
        """
        for row_keys in rows:
            row_layout = QHBoxLayout()
            row_layout.setContentsMargins(0, 0, 0, 0)
            row_layout.setSpacing(4)
            row_btns: list[QPushButton] = []
            for key in row_keys:
                btn = QPushButton(key)
                btn.setFont(btn_font)
                btn.setFocusPolicy(Qt.FocusPolicy.NoFocus)
                # Wider buttons for special keys
                if key == "Space":
                    btn.setMinimumWidth(200)
                    btn.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
                    bg = "#2a2a2a"
                elif key in ("⇧", "⌫", "Enter", "⌨", "123", "ABC"):
                    btn.setMinimumWidth(68)
                    bg = "#3a3a3a"
                else:
                    btn.setMinimumWidth(48)
                    btn.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
                    bg = "#2d2d2d"
                btn.setStyleSheet(btn_style.format(bg=bg, h=btn_h))
                # Read label at click-time so relabelled buttons work correctly
                btn.clicked.connect(lambda checked, b=btn: self._on_key(b.text()))
                row_layout.addWidget(btn)
                row_btns.append(btn)
            self._buttons.append(row_btns)
            self._outer.addLayout(row_layout)

    # ── Key handling ───────────────────────────────────────────────

    def _on_key(self, key: str):
        # Close button must always work, regardless of target widget state
        if key == "⌨":
            self.hide()
            return

        w = self._target_widget
        if w is None:
            return
        # Guard against deleted C++ object
        try:
            w.isVisible()
        except RuntimeError:
            self._target_widget = None
            return
        # Resolve the inner QLineEdit for spin-boxes / combo-boxes
        if isinstance(w, (QSpinBox, QDoubleSpinBox)):
            w = w.lineEdit()
        elif isinstance(w, QComboBox):
            w = w.lineEdit() or w
        is_line = isinstance(w, QLineEdit)
        is_multi = isinstance(w, (QTextEdit, QPlainTextEdit))
        if not is_line and not is_multi:
            return
        if key == "⇧":
            self._shifted = not self._shifted
            self._symbols = False
            self._relabel(_ROWS_UPPER if self._shifted else _ROWS_LOWER)
            return
        if key == "123":
            self._symbols = True
            self._shifted = False
            self._relabel(_ROWS_SYMBOL)
            return
        if key == "ABC":
            self._symbols = False
            self._shifted = False
            self._relabel(_ROWS_LOWER)
            return
        if key == "⌫":
            if is_line:
                w.backspace()
            else:
                tc = w.textCursor()
                tc.deletePreviousChar()
                w.setTextCursor(tc)
            return
        if key == "Enter":
            if is_line:
                w.returnPressed.emit()
            else:
                w.insertPlainText("\n")
            self.hide()
            return
        if key == "Space":
            key = " "
        # Normal character
        if is_line:
            w.insert(key)
        else:
            w.insertPlainText(key)
        # Auto-unshift after one character (fast relabel, no rebuild)
        if self._shifted and not self._symbols:
            self._shifted = False
            self._relabel(_ROWS_LOWER)

    # ── Show / position ────────────────────────────────────────────

    def _disconnect_watchers(self):
        """Disconnect any previous target-widget watchers."""
        try:
            if self._target_widget is not None:
                self._target_widget.destroyed.disconnect(self._on_target_destroyed)
        except (TypeError, RuntimeError):
            pass
        try:
            if self._watched_window is not None:
                self._watched_window.destroyed.disconnect(self._on_target_destroyed)
        except (TypeError, RuntimeError):
            pass
        self._watched_window = None

    def _on_target_destroyed(self):
        """Auto-hide when the target widget or its window is destroyed/closed."""
        self._target_widget = None
        # Reparent back to top-level so the keyboard isn't destroyed
        # along with the modal dialog that was its temporary parent.
        self._reparent_to_toplevel()
        self.hide()

    def _reparent_to_toplevel(self):
        """Move the keyboard back to a parentless top-level window."""
        if self.parent() is not None:
            flags = (Qt.WindowType.Window
                     | Qt.WindowType.FramelessWindowHint
                     | Qt.WindowType.WindowStaysOnTopHint
                     | Qt.WindowType.WindowDoesNotAcceptFocus)
            self.setParent(None, flags)
            self.setAttribute(Qt.WidgetAttribute.WA_ShowWithoutActivating, True)
            self.setFocusPolicy(Qt.FocusPolicy.NoFocus)

    def show_for(self, widget):
        """Position the keyboard below *widget* and show it on top."""
        self._disconnect_watchers()
        self._target_widget = widget
        # Watch for target widget destruction
        try:
            widget.destroyed.connect(self._on_target_destroyed)
        except Exception:
            pass
        # Watch for the parent window being closed/destroyed
        try:
            win = widget.window()
            if win is not None and win is not self:
                win.destroyed.connect(self._on_target_destroyed)
                self._watched_window = win
        except Exception:
            pass
        self._shifted = False
        self._symbols = False
        self._relabel(_ROWS_LOWER)

        # If a modal dialog is active, reparent the keyboard so it is
        # inside the modal scope and can receive clicks instead of "ding".
        modal = QApplication.activeModalWidget()
        desired_parent = widget.window() if modal is not None else None
        current_parent = self.parent()
        if desired_parent is not current_parent:
            _log(f"  reparenting keyboard: {current_parent!r} → {desired_parent!r}")
            flags = (Qt.WindowType.Window
                     | Qt.WindowType.FramelessWindowHint
                     | Qt.WindowType.WindowStaysOnTopHint
                     | Qt.WindowType.WindowDoesNotAcceptFocus)
            self.setParent(desired_parent, flags)
            self.setAttribute(Qt.WidgetAttribute.WA_ShowWithoutActivating, True)
            self.setFocusPolicy(Qt.FocusPolicy.NoFocus)

        self.adjustSize()

        # Place below the target, clamp to screen
        global_pos = widget.mapToGlobal(QPoint(0, widget.height() + 4))
        screen = QApplication.screenAt(global_pos)
        if screen is None:
            screen = QApplication.primaryScreen()
        geom = screen.availableGeometry()

        x = global_pos.x()
        y = global_pos.y()
        # Keep on-screen
        if x + self.width() > geom.right():
            x = geom.right() - self.width()
        if x < geom.left():
            x = geom.left()
        # If no room below, show above
        if y + self.height() > geom.bottom():
            y = widget.mapToGlobal(QPoint(0, 0)).y() - self.height() - 4
        if y < geom.top():
            y = geom.top()

        self.move(x, y)
        self._force_on_top()

        # Select the current value so the first key typed replaces it instead
        # of appending.  Delay slightly so it runs after the tap/click that
        # triggered the keyboard finishes positioning the cursor.
        QTimer.singleShot(10, self._select_target_all)

    def _select_target_all(self):
        """Select all text in the target so typing replaces the value."""
        w = self._target_widget
        if w is None:
            return
        try:
            if isinstance(w, (QSpinBox, QDoubleSpinBox, QAbstractSpinBox)):
                w.selectAll()
            elif isinstance(w, QComboBox):
                le = w.lineEdit()
                if le is not None:
                    le.selectAll()
            elif isinstance(w, (QLineEdit, QTextEdit, QPlainTextEdit)):
                w.selectAll()
        except RuntimeError:
            self._target_widget = None

    def show_centered(self):
        """Show the keyboard in screen centre (no target widget)."""
        self._shifted = False
        self._symbols = False
        self._relabel(_ROWS_LOWER)
        self.adjustSize()

        cursor_pos = QCursor.pos()
        screen = QApplication.screenAt(cursor_pos)
        if screen is None:
            screen = QApplication.primaryScreen()
        geom = screen.availableGeometry()

        x = geom.center().x() - self.width() // 2
        y = geom.bottom() - self.height() - 40
        self.move(x, y)
        self._force_on_top()

    def _force_on_top(self):
        """Ensure visibility above all other windows."""
        self.setWindowFlags(self.windowFlags()
                            | Qt.WindowType.WindowStaysOnTopHint)
        self.show()
        self.raise_()


# ───────────────────────────────────────────────────────────────────
#  Event filter – triple-tap / triple-click to summon keyboard
#  Also: F10 keyboard shortcut
# ───────────────────────────────────────────────────────────────────

_TAP_WINDOW = 1.2    # seconds – all 3 taps must land inside this
_TAP_RADIUS = 130    # pixels – taps must be near each other


class _TripleTapFilter(QObject):
    """App-wide event filter: three quick taps/clicks in the same spot → keyboard.

    Counts MouseButtonPress / TouchBegin events.  When three arrive within
    ``_TAP_WINDOW`` seconds and within ``_TAP_RADIUS`` pixels of each other,
    the keyboard is shown for the currently-focused text-input widget.
    """

    # Event types we count as "taps"
    # NOTE: MouseButtonDblClick is required because Qt replaces the second
    # MouseButtonPress with a MouseButtonDblClick when a double-click is
    # detected.  Without it, a mouse triple-click only registers 2 presses
    # and the keyboard never opens.
    _TAP_EVENTS = frozenset({
        QEvent.Type.MouseButtonPress,
        QEvent.Type.MouseButtonDblClick,
    })
    # Touch events (numeric fallback in case enum not present)
    try:
        _TAP_EVENTS = _TAP_EVENTS | frozenset({QEvent.Type.TouchBegin})
    except Exception:
        pass

    def __init__(self, parent=None):
        super().__init__(parent)
        self._tap_times: list[float] = []
        self._tap_positions: list[tuple[int, int]] = []
        self._last_event_time: float = 0.0  # debounce Touch+Mouse dupes
        _log("filter created")

    # ── helpers ────────────────────────────────────────────────────

    @staticmethod
    def _resolve_text_widget(w):
        """If *w* is (or wraps) an editable text widget, return it."""
        if w is None:
            return None
        if isinstance(w, QLineEdit) and not w.isReadOnly():
            return w
        if isinstance(w, (QSpinBox, QDoubleSpinBox)):
            le = w.lineEdit()
            if le and not le.isReadOnly():
                return w
        if isinstance(w, QComboBox) and w.isEditable():
            return w
        if isinstance(w, (QTextEdit, QPlainTextEdit)) and not w.isReadOnly():
            return w
        # Walk parent chain
        parent = w
        for _ in range(8):
            parent = parent.parent() if hasattr(parent, "parent") else None
            if parent is None:
                break
            if isinstance(parent, QLineEdit) and not parent.isReadOnly():
                return parent
            if isinstance(parent, (QSpinBox, QDoubleSpinBox)):
                le = parent.lineEdit()
                if le and not le.isReadOnly():
                    return parent
            if isinstance(parent, QComboBox) and parent.isEditable():
                return parent
            if isinstance(parent, (QTextEdit, QPlainTextEdit)) and not parent.isReadOnly():
                return parent
        return None

    @staticmethod
    def _widget_in_keyboard(w):
        """True if *w* is the keyboard or one of its descendants."""
        kb = TouchKeyboard._instance
        if kb is None or w is None:
            return False
        p = w
        for _ in range(12):
            if p is kb:
                return True
            p = p.parent() if hasattr(p, "parent") else None
            if p is None or not isinstance(p, QWidget):
                break
        return False

    # ── filter ─────────────────────────────────────────────────────

    def eventFilter(self, obj, event):
        try:
            return self._eventFilter(obj, event)
        except RuntimeError:
            # Wrapped C++ object has been deleted — uninstall ourselves
            try:
                from PyQt6.QtWidgets import QApplication
                app = QApplication.instance()
                if app is not None:
                    app.removeEventFilter(self)
            except Exception:
                pass
            return False
        except Exception:
            # A single misbehaving widget (e.g. one that shadows window()/
            # parent() with a plain attribute) must never be allowed to raise
            # out of this application-wide filter: doing so silently breaks
            # Qt's event dispatch and destabilises the whole app.
            _log(f"eventFilter suppressed error: {traceback.format_exc()}")
            return False

    def _eventFilter(self, obj, event):
        etype = event.type()

        # Auto-hide keyboard when a window/dialog closes or hides
        if etype in (QEvent.Type.Close, QEvent.Type.Hide):
            kb = TouchKeyboard._instance
            if kb is not None and kb.isVisible():
                # Don't react to the keyboard's own hide
                if obj is kb:
                    pass
                elif kb._target_widget is not None:
                    try:
                        target_win = kb._target_widget.window()
                        if obj is target_win or obj is kb._target_widget:
                            kb._reparent_to_toplevel()
                            kb.hide()
                    except (RuntimeError, AttributeError):
                        kb._reparent_to_toplevel()
                        kb.hide()

        # Auto-show / retarget / hide the keyboard based on focus changes.
        # Tapping (or clicking) into an editable text widget is the most
        # reliable trigger on a touch screen, so we open the keyboard the
        # moment such a widget receives user-initiated focus.  This replaces
        # the fragile triple-tap counting as the primary trigger.
        if etype == QEvent.Type.FocusIn:
            try:
                w = obj if isinstance(obj, QWidget) else None
                if w is not None and not self._widget_in_keyboard(w):
                    target = self._resolve_text_widget(w)
                    kb = TouchKeyboard._instance
                    if target is not None:
                        try:
                            reason = event.reason()
                        except Exception:
                            reason = None
                        user_initiated = reason in (
                            Qt.FocusReason.MouseFocusReason,
                            Qt.FocusReason.PopupFocusReason,
                        )
                        already_visible = kb is not None and kb.isVisible()
                        if user_initiated or already_visible:
                            kb = TouchKeyboard.instance(None)
                            if kb._target_widget is not target or not kb.isVisible():
                                kb.show_for(target)
                    elif kb is not None and kb.isVisible():
                        # Focus moved to a non-text widget — dismiss keyboard
                        kb._reparent_to_toplevel()
                        kb.hide()
            except (RuntimeError, AttributeError):
                pass

        if etype not in self._TAP_EVENTS:
            return False

        # Ignore taps/clicks that land on the virtual keyboard itself;
        # fast typing would otherwise trigger a false triple-tap.
        kb = TouchKeyboard._instance
        if kb is not None:
            try:
                # Only trust window() if it is still the bound Qt method; some
                # widgets shadow it with a plain attribute, which would raise
                # "object is not callable" when invoked here.
                win_attr = getattr(obj, 'window', None)
                obj_win = win_attr() if callable(win_attr) else None
                if obj is kb or obj_win is kb:
                    return False
            except (RuntimeError, AttributeError, TypeError):
                pass
            # Also check by widget-at for touch events
            try:
                w = obj if isinstance(obj, QWidget) else None
                while w is not None:
                    if w is kb:
                        return False
                    w = w.parent() if hasattr(w, 'parent') else None
                    if w is not None and not isinstance(w, QWidget):
                        break
            except (RuntimeError, AttributeError):
                pass

        now = time.monotonic()

        # Debounce: touchscreens send TouchBegin + synthesised MouseButtonPress
        # for a single physical tap.  Use a small window so real rapid mouse
        # clicks (triple-click) are not discarded.
        if (now - self._last_event_time) < 0.015:
            return False
        self._last_event_time = now

        # Get global position of this tap
        try:
            gpos = event.globalPosition()
            px, py = int(gpos.x()), int(gpos.y())
        except AttributeError:
            try:
                gpos = event.globalPos()
                px, py = gpos.x(), gpos.y()
            except Exception:
                px, py = 0, 0

        self._tap_times.append(now)
        self._tap_positions.append((px, py))

        # Prune taps older than the window
        cutoff = now - _TAP_WINDOW
        while self._tap_times and self._tap_times[0] < cutoff:
            self._tap_times.pop(0)
            self._tap_positions.pop(0)

        if len(self._tap_times) >= 3:
            # Check spatial proximity of the last 3 taps
            pts = self._tap_positions[-3:]
            xs = [p[0] for p in pts]
            ys = [p[1] for p in pts]
            dx = max(xs) - min(xs)
            dy = max(ys) - min(ys)
            if dx <= _TAP_RADIUS and dy <= _TAP_RADIUS:
                _log(f"triple-tap detected  (dx={dx} dy={dy})")
                self._tap_times.clear()
                self._tap_positions.clear()
                # Toggle: if keyboard is already visible, hide it
                QTimer.singleShot(50, self._toggle_keyboard)
            # If taps were too spread out, don't clear — let the window
            # prune naturally so a valid triple-tap can still fire

        return False  # never consume the event

    def _toggle_keyboard(self):
        """Show the keyboard for the focused text widget (triple-tap only opens, never closes)."""
        _log("_toggle_keyboard called (triple-tap)")
        kb = TouchKeyboard._instance

        # Find the current text widget under focus / cursor
        fw = QApplication.focusWidget()
        target = self._resolve_text_widget(fw)
        _log(f"  focusWidget={fw!r}  target={target!r}")

        if target is None:
            w_at = QApplication.widgetAt(QCursor.pos())
            target = self._resolve_text_widget(w_at)
            _log(f"  widgetAt cursor={w_at!r}  target={target!r}")

        # If keyboard is already showing, retarget if different widget.
        # Triple-tap is now only a fallback that opens/retargets — it never
        # hides, so it can't fight the focus-based auto-show.
        if kb is not None and kb.isVisible():
            if target is not None and kb._target_widget is not target:
                kb.show_for(target)
                _log("  keyboard retargeted to new widget")
            else:
                _log("  keyboard already visible — left open on triple-tap")
            return

        kb = TouchKeyboard.instance(None)
        if target is not None:
            kb.show_for(target)
            _log("  keyboard shown for target")
        else:
            _log("  no text widget focused — keyboard suppressed (not a text-input triple-tap)")


def _toggle_keyboard():
    """Called by the F10 shortcut or button press."""
    kb = TouchKeyboard.instance(None)
    # Find current text target
    fw = QApplication.focusWidget()
    target = _TripleTapFilter._resolve_text_widget(fw)
    if target is None:
        w_at = QApplication.widgetAt(QCursor.pos())
        target = _TripleTapFilter._resolve_text_widget(w_at)
    # If visible and same target → toggle off; different target → retarget
    if kb.isVisible():
        if target is not None and kb._target_widget is target:
            kb.hide()
        elif target is not None:
            kb.show_for(target)
        else:
            kb.hide()
        return
    if target is not None:
        kb.show_for(target)
    else:
        kb.show_centered()


def _cleanup_keyboard():
    """Destroy the keyboard widget so it doesn't linger after app exit."""
    kb = TouchKeyboard._instance
    if kb is not None:
        try:
            kb.hide()
            kb.deleteLater()
        except RuntimeError:
            pass  # C++ object already destroyed during Qt shutdown
        TouchKeyboard._instance = None
    _log("keyboard cleaned up on app quit")


def install_touch_keyboard(app: QApplication):
    """Install triple-tap filter + F10 shortcut on *app*.

    Call once from gui.py ``__init__`` after the QApplication is created.
    """
    _log("installing touch keyboard filter …")
    # Event filter for triple-tap
    filt = _TripleTapFilter(app)
    app.installEventFilter(filt)
    app._touch_kb_filter = filt   # prevent GC

    # Ensure keyboard is destroyed when the application quits
    app.aboutToQuit.connect(_cleanup_keyboard)

    # Global F10 shortcut as a reliable fallback
    try:
        for win in app.topLevelWidgets():
            sc = QShortcut(QKeySequence(Qt.Key.Key_F10), win)
            sc.setContext(Qt.ShortcutContext.ApplicationShortcut)
            sc.activated.connect(_toggle_keyboard)
            win._touch_kb_shortcut = sc  # prevent GC
            _log(f"  F10 shortcut on {win!r}")
            break
    except Exception:
        _log(f"  F10 shortcut failed: {traceback.format_exc()}")

    _log("touch keyboard filter installed ✓")
