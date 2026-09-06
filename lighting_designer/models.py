"""
Lighting Designer Data Models
Data structures for fixtures, patches, and projects.
"""

from dataclasses import dataclass, field
from typing import Optional
import json
import os

try:
    from .fixture_sequence import FixtureSequence
except ImportError:
    from fixture_sequence import FixtureSequence


@dataclass
class FixtureChannel:
    """A single channel within a fixture."""
    name: str
    type: str  # 'dimmer', 'red', 'green', 'blue', 'white', 'pan', 'tilt', 'gobo', 'color_wheel', 'effect', etc.
    default: int = 0
    min_value: int = 0
    max_value: int = 255
    # For color wheels: list of {"name": "Red", "value": 10, "color": "#ff0000"}
    color_wheel_colors: list[dict] = field(default_factory=list)
    # For effect/macro channels: list of {"name": "Strobe Slow", "value": 50, "value_end": 100}
    # value_end is optional - if present it's a range, otherwise single value
    effect_values: list[dict] = field(default_factory=list)
    # For gobos: list of {"name": "Circle", "value": 10}
    gobo_slots: list[dict] = field(default_factory=list)
    # For on_off channels: DMX values for off and on states
    on_value: int = 255
    off_value: int = 0

    def __post_init__(self):
        # Cache lowered type string to avoid thousands of .lower() calls
        # in the 40fps effect engine hot path.
        self._type_lower: str = self.type.lower() if self.type else ''

    @property
    def type_lower(self) -> str:
        try:
            return self._type_lower
        except AttributeError:
            self._type_lower = self.type.lower() if self.type else ''
            return self._type_lower


@dataclass
class FixtureMode:
    """A mode configuration for a fixture (different channel counts/layouts)."""
    name: str
    channels: list[FixtureChannel] = field(default_factory=list)
    
    @property
    def channel_count(self) -> int:
        return len(self.channels)


@dataclass
class FixtureProfile:
    """A fixture type definition (from OFL or custom)."""
    manufacturer: str
    name: str
    category: str  # 'Moving Head', 'Par', 'Dimmer', 'Strobe', etc.
    modes: list[FixtureMode] = field(default_factory=list)
    ofl_key: Optional[str] = None  # OFL fixture key if from library
    is_custom: bool = False
    
    # Pixel mapping configuration (applies to all fixtures of this type)
    is_pixel_fixture: bool = False  # True if this fixture type has addressable pixels
    pixel_rows: int = 1  # Number of rows in pixel grid
    pixel_columns: int = 1  # Number of columns in pixel grid
    channels_per_pixel: int = 3  # 1=Dimmer, 3=RGB, 4=RGBW
    pixel_channel_offset: int = 0  # First pixel starts at base address + this offset
    pixel_channel_table: list[dict] = field(default_factory=list)  # Per-pixel channel mapping
    
    @property
    def full_name(self) -> str:
        return f"{self.manufacturer} {self.name}"
    
    @property
    def profile_id(self) -> str:
        """Unique identifier for this profile type."""
        return f"{self.manufacturer}:{self.name}"
    
    def get_mode(self, mode_name: str) -> Optional[FixtureMode]:
        for mode in self.modes:
            if mode.name == mode_name:
                return mode
        return None
    
    def to_dict(self) -> dict:
        return {
            'manufacturer': self.manufacturer,
            'name': self.name,
            'category': self.category,
            'modes': [
                {
                    'name': m.name,
                    'channels': [
                        {
                            'name': c.name, 
                            'type': c.type, 
                            'default': c.default,
                            'color_wheel_colors': c.color_wheel_colors if c.color_wheel_colors else None,
                            'effect_values': c.effect_values if c.effect_values else None,
                            'gobo_slots': c.gobo_slots if c.gobo_slots else None,
                            'on_value': c.on_value if c.type == 'on_off' else None,
                            'off_value': c.off_value if c.type == 'on_off' else None
                        }
                        for c in m.channels
                    ]
                }
                for m in self.modes
            ],
            'ofl_key': self.ofl_key,
            'is_custom': self.is_custom,
            # Pixel mapping
            'is_pixel_fixture': self.is_pixel_fixture,
            'pixel_rows': self.pixel_rows,
            'pixel_columns': self.pixel_columns,
            'channels_per_pixel': self.channels_per_pixel,
            'pixel_channel_offset': self.pixel_channel_offset,
            'pixel_channel_table': self.pixel_channel_table
        }
    
    def auto_fill_pixel_table(self, pattern: str = "sequential"):
        """Auto-fill the pixel channel table with common patterns.
        
        Args:
            pattern: 'sequential' (L-R, top-bottom), 'snake' (alternating direction),
                    'columns_up' (column-by-column, bottom-to-top),
                    'columns_down' (column-by-column, top-to-bottom),
                    'right_to_left' (R-L, top-bottom),
                    'rtl_bottom_up' (R-L, bottom-to-top),
                    'ltr_bottom_up' (L-R, bottom-to-top),
                    'snake_vertical' (snake by columns)
        """
        self.pixel_channel_table = []
        pixel_num = 1
        channel_offset = self.pixel_channel_offset
        
        def _add_pixel(row, col):
            nonlocal pixel_num, channel_offset
            pixel_data = {'row': row, 'col': col, 'pixel_num': pixel_num}
            if self.channels_per_pixel == 1:
                pixel_data['dimmer'] = channel_offset
                channel_offset += 1
            elif self.channels_per_pixel == 3:
                pixel_data['red'] = channel_offset
                pixel_data['green'] = channel_offset + 1
                pixel_data['blue'] = channel_offset + 2
                channel_offset += 3
            elif self.channels_per_pixel == 4:
                pixel_data['red'] = channel_offset
                pixel_data['green'] = channel_offset + 1
                pixel_data['blue'] = channel_offset + 2
                pixel_data['white'] = channel_offset + 3
                channel_offset += 4
            self.pixel_channel_table.append(pixel_data)
            pixel_num += 1
        
        # Right to Left pattern: rows top-to-bottom, columns right-to-left
        if pattern == "right_to_left":
            for row in range(1, self.pixel_rows + 1):
                for col in range(self.pixel_columns, 0, -1):
                    _add_pixel(row, col)
            return
        
        # Right to Left Bottom to Top: rows bottom-to-top, columns right-to-left
        if pattern == "rtl_bottom_up":
            for row in range(self.pixel_rows, 0, -1):
                for col in range(self.pixel_columns, 0, -1):
                    _add_pixel(row, col)
            return
        
        # Left to Right Bottom to Top: rows bottom-to-top, columns left-to-right
        if pattern == "ltr_bottom_up":
            for row in range(self.pixel_rows, 0, -1):
                for col in range(1, self.pixel_columns + 1):
                    _add_pixel(row, col)
            return
        
        # Columns Up pattern: iterate columns first, rows bottom-to-top
        if pattern == "columns_up":
            for col in range(1, self.pixel_columns + 1):
                for row in range(self.pixel_rows, 0, -1):
                    _add_pixel(row, col)
            return
        
        # Columns Down pattern: iterate columns first, rows top-to-bottom
        if pattern == "columns_down":
            for col in range(1, self.pixel_columns + 1):
                for row in range(1, self.pixel_rows + 1):
                    _add_pixel(row, col)
            return
        
        # Snake Vertical: columns left-to-right, alternating row direction
        if pattern == "snake_vertical":
            for col in range(1, self.pixel_columns + 1):
                rows = range(1, self.pixel_rows + 1) if col % 2 == 1 else range(self.pixel_rows, 0, -1)
                for row in rows:
                    _add_pixel(row, col)
            return
        
        # Standard row-based patterns (sequential, snake)
        for row in range(1, self.pixel_rows + 1):
            cols_range = range(1, self.pixel_columns + 1)
            # Snake pattern reverses direction on even rows
            if pattern == "snake" and row % 2 == 0:
                cols_range = reversed(list(cols_range))
            
            for col in cols_range:
                _add_pixel(row, col)
    
    @classmethod
    def from_dict(cls, data: dict) -> 'FixtureProfile':
        modes = []
        for m in data.get('modes', []):
            channels = [
                FixtureChannel(
                    name=c['name'],
                    type=c['type'],
                    default=c.get('default', 0),
                    color_wheel_colors=c.get('color_wheel_colors') or [],
                    effect_values=c.get('effect_values') or [],
                    gobo_slots=c.get('gobo_slots') or [],
                    on_value=c.get('on_value', 255),
                    off_value=c.get('off_value', 0)
                )
                for c in m.get('channels', [])
            ]
            modes.append(FixtureMode(name=m['name'], channels=channels))
        
        return cls(
            manufacturer=data['manufacturer'],
            name=data['name'],
            category=data.get('category', 'Other'),
            modes=modes,
            ofl_key=data.get('ofl_key'),
            is_custom=data.get('is_custom', False),
            # Pixel mapping
            is_pixel_fixture=data.get('is_pixel_fixture', False),
            pixel_rows=data.get('pixel_rows', 1),
            pixel_columns=data.get('pixel_columns', 1),
            channels_per_pixel=data.get('channels_per_pixel', 3),
            pixel_channel_offset=data.get('pixel_channel_offset', 0),
            pixel_channel_table=data.get('pixel_channel_table', [])
        )


@dataclass
class PatchedFixture:
    """A fixture instance in the patch."""
    id: str  # Unique identifier
    profile: FixtureProfile
    mode_name: str
    universe: int
    address: int  # 1-512
    label: str = ""
    home_pan: Optional[int] = None  # Home/default pan position (0-255)
    home_tilt: Optional[int] = None  # Home/default tilt position (0-255)
    location_x: float = 0.5  # X position on stage (0.0 = left, 1.0 = right)
    location_y: float = 0.5  # Y position on stage (0.0 = back, 1.0 = front)
    # Beam direction calibration (for stage preview visualization)
    pan_offset: float = 0.0  # Degrees to offset pan visualization (-180 to +180)
    pan_invert: bool = False  # Invert pan direction
    pan_range: float = 540.0  # Total pan range in degrees (common: 540, 630)
    tilt_offset: float = 0.0  # Degrees to offset tilt visualization (-90 to +90)
    tilt_invert: bool = False  # Invert tilt direction
    tilt_range: float = 270.0  # Total tilt range in degrees (common: 270, 180)
    
    # Pixel mapping fields
    is_pixel_mapped: bool = False  # True if fixture has addressable pixels
    pixel_rows: int = 1  # Number of rows in pixel grid
    pixel_columns: int = 1  # Number of columns in pixel grid
    channels_per_pixel: int = 3  # 1=Dimmer, 3=RGB, 4=RGBW
    pixel_channel_order: list[str] = field(default_factory=lambda: ["red", "green", "blue"])
    pixel_channel_offset: int = 0  # First pixel starts at base address + this offset
    pixel_channel_table: list[dict] = field(default_factory=list)  # Per-pixel channel mapping
    
    # Visual size in LOCATION preview (for pixel fixtures)
    visual_width: float = 0.1  # Width as fraction of stage (0.0 to 1.0)
    visual_height: float = 0.05  # Height as fraction of stage (0.0 to 1.0)
    fixture_rotation: int = 0  # Rotation in degrees (0, 90, 180, 270)
    
    # Effect exclusion
    exclude_from_effects: bool = False  # When True, effects/presets will not control this fixture
    exclude_from_overlay: bool = False  # When True, video overlay will not drive this fixture
    
    @property
    def mode(self) -> Optional[FixtureMode]:
        return self.profile.get_mode(self.mode_name)
    
    @property
    def channel_count(self) -> int:
        mode = self.mode
        return mode.channel_count if mode else 0
    
    @property
    def end_address(self) -> int:
        return self.address + self.channel_count - 1
    
    @property
    def name(self) -> str:
        """Alias for label for backwards compatibility."""
        return self.label
    
    @property
    def has_home_position(self) -> bool:
        """Check if fixture has a home position defined."""
        return self.home_pan is not None or self.home_tilt is not None
    
    @property
    def total_pixels(self) -> int:
        """Return total number of pixels in the grid."""
        return self.pixel_rows * self.pixel_columns
    
    def get_pixel_channels(self, pixel_num: int) -> dict:
        """Get channel offsets for a specific pixel (1-indexed).
        
        Returns dict with channel offsets from base address, e.g.:
        {'red': 0, 'green': 1, 'blue': 2} for RGB pixel 1
        """
        if not self.pixel_channel_table:
            return {}
        for pixel in self.pixel_channel_table:
            if pixel.get('pixel_num') == pixel_num:
                return {k: v for k, v in pixel.items() if k not in ('row', 'col', 'pixel_num')}
        return {}
    
    def auto_fill_pixel_table(self, pattern: str = "sequential"):
        """Auto-fill the pixel channel table with common patterns.
        
        Args:
            pattern: 'sequential' (L-R, top-bottom), 'snake' (alternating direction),
                    'columns_up' (column-by-column, bottom-to-top),
                    'columns_down' (column-by-column, top-to-bottom),
                    'right_to_left' (R-L, top-bottom),
                    'rtl_bottom_up' (R-L, bottom-to-top),
                    'ltr_bottom_up' (L-R, bottom-to-top),
                    'snake_vertical' (snake by columns)
        """
        self.pixel_channel_table = []
        pixel_num = 1
        channel_offset = self.pixel_channel_offset
        
        def _add_pixel(row, col):
            nonlocal pixel_num, channel_offset
            pixel_data = {'row': row, 'col': col, 'pixel_num': pixel_num}
            if self.channels_per_pixel == 1:
                pixel_data['dimmer'] = channel_offset
                channel_offset += 1
            elif self.channels_per_pixel == 3:
                order = self.pixel_channel_order if self.pixel_channel_order else ['red', 'green', 'blue']
                for i, ch_type in enumerate(order[:3]):
                    pixel_data[ch_type] = channel_offset + i
                channel_offset += 3
            elif self.channels_per_pixel == 4:
                order = self.pixel_channel_order if self.pixel_channel_order else ['red', 'green', 'blue', 'white']
                for i, ch_type in enumerate(order[:4]):
                    pixel_data[ch_type] = channel_offset + i
                channel_offset += 4
            self.pixel_channel_table.append(pixel_data)
            pixel_num += 1
        
        # Right to Left pattern: rows top-to-bottom, columns right-to-left
        if pattern == "right_to_left":
            for row in range(1, self.pixel_rows + 1):
                for col in range(self.pixel_columns, 0, -1):
                    _add_pixel(row, col)
            return
        
        # Right to Left Bottom to Top: rows bottom-to-top, columns right-to-left
        if pattern == "rtl_bottom_up":
            for row in range(self.pixel_rows, 0, -1):
                for col in range(self.pixel_columns, 0, -1):
                    _add_pixel(row, col)
            return
        
        # Left to Right Bottom to Top: rows bottom-to-top, columns left-to-right
        if pattern == "ltr_bottom_up":
            for row in range(self.pixel_rows, 0, -1):
                for col in range(1, self.pixel_columns + 1):
                    _add_pixel(row, col)
            return
        
        # Columns Up pattern: iterate columns first, rows bottom-to-top
        if pattern == "columns_up":
            for col in range(1, self.pixel_columns + 1):
                for row in range(self.pixel_rows, 0, -1):
                    _add_pixel(row, col)
            return
        
        # Columns Down pattern: iterate columns first, rows top-to-bottom
        if pattern == "columns_down":
            for col in range(1, self.pixel_columns + 1):
                for row in range(1, self.pixel_rows + 1):
                    _add_pixel(row, col)
            return
        
        # Snake Vertical: columns left-to-right, alternating row direction
        if pattern == "snake_vertical":
            for col in range(1, self.pixel_columns + 1):
                rows = range(1, self.pixel_rows + 1) if col % 2 == 1 else range(self.pixel_rows, 0, -1)
                for row in rows:
                    _add_pixel(row, col)
            return
        
        # Standard row-based patterns (sequential, snake)
        for row in range(1, self.pixel_rows + 1):
            cols = range(1, self.pixel_columns + 1)
            # Snake pattern reverses direction on even rows
            if pattern == "snake" and row % 2 == 0:
                cols = reversed(cols)
            
            for col in cols:
                _add_pixel(row, col)
    
    def to_dict(self) -> dict:
        result = {
            'id': self.id,
            'profile': self.profile.to_dict(),
            'mode_name': self.mode_name,
            'universe': self.universe,
            'address': self.address,
            'label': self.label,
            'location_x': self.location_x,
            'location_y': self.location_y
        }
        if self.home_pan is not None:
            result['home_pan'] = self.home_pan
        if self.home_tilt is not None:
            result['home_tilt'] = self.home_tilt
        # Beam calibration (only save non-default values)
        if self.pan_offset != 0.0:
            result['pan_offset'] = self.pan_offset
        if self.pan_invert:
            result['pan_invert'] = self.pan_invert
        if self.pan_range != 540.0:
            result['pan_range'] = self.pan_range
        if self.tilt_offset != 0.0:
            result['tilt_offset'] = self.tilt_offset
        if self.tilt_invert:
            result['tilt_invert'] = self.tilt_invert
        if self.tilt_range != 270.0:
            result['tilt_range'] = self.tilt_range
        # Visual size (always save if non-default, for position layout)
        if self.visual_width != 0.1:
            result['visual_width'] = self.visual_width
        if self.visual_height != 0.05:
            result['visual_height'] = self.visual_height
        if self.fixture_rotation != 0:
            result['fixture_rotation'] = self.fixture_rotation
        # Pixel mapping (only save if enabled)
        if self.is_pixel_mapped:
            result['is_pixel_mapped'] = True
            result['pixel_rows'] = self.pixel_rows
            result['pixel_columns'] = self.pixel_columns
            result['channels_per_pixel'] = self.channels_per_pixel
            result['pixel_channel_order'] = self.pixel_channel_order
            result['pixel_channel_offset'] = self.pixel_channel_offset
            result['pixel_channel_table'] = self.pixel_channel_table
        if self.exclude_from_effects:
            result['exclude_from_effects'] = True
        if self.exclude_from_overlay:
            result['exclude_from_overlay'] = True
        return result
    
    @classmethod
    def from_dict(cls, data: dict) -> 'PatchedFixture':
        return cls(
            id=data['id'],
            profile=FixtureProfile.from_dict(data['profile']),
            mode_name=data['mode_name'],
            universe=data['universe'],
            address=data['address'],
            label=data.get('label', ''),
            home_pan=data.get('home_pan'),
            home_tilt=data.get('home_tilt'),
            location_x=data.get('location_x', 0.5),
            location_y=data.get('location_y', 0.5),
            # Beam calibration
            pan_offset=data.get('pan_offset', 0.0),
            pan_invert=data.get('pan_invert', False),
            pan_range=data.get('pan_range', 540.0),
            tilt_offset=data.get('tilt_offset', 0.0),
            tilt_invert=data.get('tilt_invert', False),
            tilt_range=data.get('tilt_range', 270.0),
            # Pixel mapping
            is_pixel_mapped=data.get('is_pixel_mapped', False),
            pixel_rows=data.get('pixel_rows', 1),
            pixel_columns=data.get('pixel_columns', 1),
            channels_per_pixel=data.get('channels_per_pixel', 3),
            pixel_channel_order=data.get('pixel_channel_order', ['red', 'green', 'blue']),
            pixel_channel_offset=data.get('pixel_channel_offset', 0),
            pixel_channel_table=data.get('pixel_channel_table', []),
            visual_width=data.get('visual_width', 0.1),
            visual_height=data.get('visual_height', 0.05),
            fixture_rotation=data.get('fixture_rotation', 0),
            exclude_from_effects=data.get('exclude_from_effects', False),
            exclude_from_overlay=data.get('exclude_from_overlay', False)
        )


@dataclass
class EffectLayer:
    """A single layer in a stacked effect preset.

    Each layer controls one aspect (color, movement, strobe, etc.) and targets
    a specific fixture group.  Multiple layers are merged at runtime via HTP
    for intensity and LTP (most-recent wins) for other channels.
    """
    id: str
    name: str = "Layer"
    enabled: bool = True
    # What this layer controls
    layer_type: str = "color"  # color, movement, strobe, intensity, effect, gobo, position
    # Target group (empty or ["all"] = all fixtures)
    target_groups: list[str] = field(default_factory=lambda: ["all"])
    target_fixtures: list[str] = field(default_factory=list)
    # Core parameters
    color: str = "#ffffff"
    color_palette: list[str] = field(default_factory=list)
    rainbow_colors: bool = False
    effect_type: str = "static"
    intensity: int = 100
    intensity_min: int = 0
    intensity_max: int = 100
    speed_bpm: int = 120
    cycle_seconds: float = 0.0
    direction: str = "forward"
    fixture_offset: float = 0.25
    # Movement
    movement_pattern: str = "none"
    pan_min: int = 0
    pan_max: int = 255
    tilt_min: int = 64
    tilt_max: int = 192
    # Position cycling
    position_cycle_enabled: bool = False
    position_cycle_presets: list[str] = field(default_factory=list)
    position_cycle_hold_time: float = 4.0
    position_cycle_speed: int = 0  # Pan/Tilt speed DMX (0 = fastest on most fixtures)
    # Channels
    gobo_value: int = 0
    gobo_rotation_value: int = 0
    gobo2_value: int = 0
    gobo2_rotation_value: int = 0
    color_wheel_value: int = -1
    macro_value: int = 0
    effect_channel_value: int = -1
    # Fixture-specific DMX overrides
    prism_value: int = 0
    prism_rotation: int = 0
    prism2_value: int = 0
    prism2_rotation: int = 0
    focus_value: int = -1
    zoom_value: int = -1
    frost_value: int = 0
    shutter_value: int = -1
    # Dimmer effect mode (for dimmer layer type)
    dimmer_effect: str = "on"  # on, fade, random_fade, odd_even, left_right, etc.
    # Position preset (for position layer type)
    position_preset: str = ""  # Name/ID of the position preset to apply
    # Speed multiplier
    master_speed: int = 100
    # Other channel values (for 'other' layer type) — maps channel_type → DMX value
    other_channel_values: dict = field(default_factory=dict)

    def to_dict(self) -> dict:
        return {
            'id': self.id, 'name': self.name, 'enabled': self.enabled,
            'layer_type': self.layer_type,
            'target_groups': self.target_groups,
            'target_fixtures': self.target_fixtures,
            'color': self.color, 'color_palette': self.color_palette,
            'rainbow_colors': self.rainbow_colors,
            'effect_type': self.effect_type,
            'intensity': self.intensity,
            'intensity_min': self.intensity_min,
            'intensity_max': self.intensity_max,
            'speed_bpm': self.speed_bpm, 'cycle_seconds': self.cycle_seconds,
            'direction': self.direction, 'fixture_offset': self.fixture_offset,
            'movement_pattern': self.movement_pattern,
            'pan_min': self.pan_min, 'pan_max': self.pan_max,
            'tilt_min': self.tilt_min, 'tilt_max': self.tilt_max,
            'position_cycle_enabled': self.position_cycle_enabled,
            'position_cycle_presets': self.position_cycle_presets,
            'position_cycle_hold_time': self.position_cycle_hold_time,
            'position_cycle_speed': self.position_cycle_speed,
            'gobo_value': self.gobo_value,
            'gobo_rotation_value': self.gobo_rotation_value,
            'gobo2_value': self.gobo2_value,
            'gobo2_rotation_value': self.gobo2_rotation_value,
            'color_wheel_value': self.color_wheel_value,
            'macro_value': self.macro_value,
            'effect_channel_value': self.effect_channel_value,
            'prism_value': self.prism_value,
            'prism_rotation': self.prism_rotation,
            'prism2_value': self.prism2_value,
            'prism2_rotation': self.prism2_rotation,
            'focus_value': self.focus_value,
            'zoom_value': self.zoom_value,
            'frost_value': self.frost_value,
            'shutter_value': self.shutter_value,
            'dimmer_effect': self.dimmer_effect,
            'position_preset': self.position_preset,
            'master_speed': self.master_speed,
            'other_channel_values': dict(self.other_channel_values),
            # GUI multi-aspect tracking — must round-trip so that a saved
            # layer whose layer_type is '' (multi-aspect, e.g. Color+Dimmer)
            # still reports the correct engine routing (dimmer_fx, strobe…)
            # after reload.  Without this, to_effect_params() can only see
            # layer_type='' and falls back to a plain static color, which
            # surfaces as "lights just turn on, dimmer effect missing".
            '_ui_type_key': getattr(self, '_ui_type_key', None),
            '_touched_types': sorted(getattr(self, '_touched_types', set())),
        }

    @classmethod
    def from_dict(cls, data: dict) -> 'EffectLayer':
        obj = cls(
            id=data['id'], name=data.get('name', 'Layer'),
            enabled=data.get('enabled', True),
            layer_type=data.get('layer_type', 'color'),
            target_groups=data.get('target_groups', ['all']),
            target_fixtures=data.get('target_fixtures', []),
            color=data.get('color', '#ffffff'),
            color_palette=data.get('color_palette', []),
            rainbow_colors=data.get('rainbow_colors', False),
            effect_type=data.get('effect_type', 'static'),
            intensity=data.get('intensity', 100),
            intensity_min=data.get('intensity_min', 0),
            intensity_max=data.get('intensity_max', 100),
            speed_bpm=data.get('speed_bpm', 120),
            cycle_seconds=data.get('cycle_seconds', 0.0),
            direction=data.get('direction', 'forward'),
            fixture_offset=float(data.get('fixture_offset', 0.25)),
            movement_pattern=data.get('movement_pattern', 'none'),
            pan_min=data.get('pan_min', 0), pan_max=data.get('pan_max', 255),
            tilt_min=data.get('tilt_min', 64), tilt_max=data.get('tilt_max', 192),
            position_cycle_enabled=data.get('position_cycle_enabled', False),
            position_cycle_presets=data.get('position_cycle_presets', []),
            position_cycle_hold_time=data.get('position_cycle_hold_time', 4.0),
            position_cycle_speed=data.get('position_cycle_speed', 0),
            gobo_value=data.get('gobo_value', 0),
            gobo_rotation_value=data.get('gobo_rotation_value', 0),
            gobo2_value=data.get('gobo2_value', 0),
            gobo2_rotation_value=data.get('gobo2_rotation_value', 0),
            color_wheel_value=data.get('color_wheel_value', -1),
            macro_value=data.get('macro_value', 0),
            effect_channel_value=data.get('effect_channel_value', -1),
            prism_value=data.get('prism_value', 0),
            prism_rotation=data.get('prism_rotation', 0),
            prism2_value=data.get('prism2_value', 0),
            prism2_rotation=data.get('prism2_rotation', 0),
            focus_value=data.get('focus_value', -1),
            zoom_value=data.get('zoom_value', -1),
            frost_value=data.get('frost_value', 0),
            shutter_value=data.get('shutter_value', -1),
            dimmer_effect=data.get('dimmer_effect', 'on'),
            position_preset=data.get('position_preset', ''),
            master_speed=data.get('master_speed', 100),
            other_channel_values=dict(data.get('other_channel_values', {})),
        )
        # Restore GUI multi-aspect tracking attributes that aren't dataclass
        # fields.  These drive effect_type routing for layers saved with
        # layer_type='' (Color+Dimmer, Color+Strobe, etc.).
        ui_key = data.get('_ui_type_key')
        if ui_key:
            obj._ui_type_key = ui_key
        touched = data.get('_touched_types')
        if touched:
            try:
                obj._touched_types = set(touched)
            except TypeError:
                pass
        return obj

    def to_effect_params(self) -> 'EffectParameters':
        """Convert this layer to an EffectParameters for the engine.
        
        Maps layer_type to a sensible effect_type if one isn't already set.
        Imported lazily to avoid circular imports.
        """
        try:
            from .effect_engine import EffectParameters
        except ImportError:
            from effect_engine import EffectParameters

        # Determine effect_type from layer_type + user setting
        etype = self.effect_type
        if self.layer_type == "strobe":
            etype = "strobe"
        elif self.layer_type == "intensity" and etype == "static":
            # Only animate (pulse) when the user deliberately set a
            # range *and* it doesn't look like un-touched defaults.
            # The default EffectLayer has intensity_min=0, intensity_max=100
            # which would incorrectly create a pulse for look presets.
            if (self.intensity_min != self.intensity_max
                    and not (self.intensity_min == 0 and self.intensity_max == 100)):
                etype = "pulse"
        elif self.layer_type == "movement":
            etype = "static"  # movement layers NEVER run color animations
        elif self.layer_type == "color" and etype == "static":
            etype = "static"  # explicit — color layer defaults to static
        elif self.layer_type == 'position':
            etype = "static"  # position layers just set pan/tilt from a preset
        elif self.layer_type in ('gobo', 'prism', 'optics', 'fx_channel'):
            etype = "static"  # discrete-channel layers are always static
        elif self.layer_type == 'smoke':
            etype = "static"  # smoke layers output a fixed DMX value
        elif self.layer_type == 'other':
            etype = "static"  # other layers output fixed DMX values for uncategorized channels
        elif self.layer_type == 'dimmer':
            etype = "dimmer_fx"  # dimmer layers use the dimmer effect engine
        elif self.layer_type == 'pixel':
            pass  # pixel layer — etype already set from pixel effect buttons
        elif self.layer_type == '':
            # Multi-aspect or unset layer_type — fall back to _ui_type_key
            # (set by the GUI when the user last clicked a type button) so
            # dimmer / strobe / etc. still route to the correct engine path.
            ui_key = getattr(self, '_ui_type_key', None)
            if ui_key == 'dimmer':
                etype = "dimmer_fx"
            elif ui_key == 'strobe':
                etype = "strobe"
            elif ui_key == 'movement':
                etype = "static"
            # else: keep existing etype (color/effect/etc.)

        # Movement pattern: always pass through if set (not restricted by layer_type)
        mpat = self.movement_pattern if self.movement_pattern and self.movement_pattern.lower() not in ('none', '') else "none"

        return EffectParameters(
            layer_type=self.layer_type,
            target_groups=list(self.target_groups),
            target_fixtures=list(self.target_fixtures),
            color=self.color,
            color_palette=list(self.color_palette),
            rainbow_colors=self.rainbow_colors,
            effect_type=etype,
            intensity=self.intensity,
            intensity_min=self.intensity_min,
            intensity_max=self.intensity_max,
            speed_bpm=self.speed_bpm,
            cycle_seconds=self.cycle_seconds,
            direction=self.direction,
            fixture_offset=self.fixture_offset,
            movement_pattern=mpat,
            pan_min=self.pan_min, pan_max=self.pan_max,
            tilt_min=self.tilt_min, tilt_max=self.tilt_max,
            position_cycle_enabled=self.position_cycle_enabled,
            position_cycle_presets=list(self.position_cycle_presets),
            position_cycle_hold_time=self.position_cycle_hold_time,
            position_cycle_speed=self.position_cycle_speed,
            gobo_value=self.gobo_value,
            gobo_rotation_value=self.gobo_rotation_value,
            gobo2_value=self.gobo2_value,
            gobo2_rotation_value=self.gobo2_rotation_value,
            color_wheel_value=self.color_wheel_value,
            macro_value=self.macro_value,
            effect_channel_value=self.effect_channel_value,
            prism_value=self.prism_value,
            prism_rotation=self.prism_rotation,
            prism2_value=self.prism2_value,
            prism2_rotation=self.prism2_rotation,
            focus_value=self.focus_value,
            zoom_value=self.zoom_value,
            frost_value=self.frost_value,
            shutter_value=self.shutter_value,
            dimmer_effect=self.dimmer_effect,
            position_preset=self.position_preset,
            master_speed=self.master_speed,
            other_channel_values=dict(self.other_channel_values),
        )


@dataclass
class EffectPreset:
    """A saved lighting effect preset."""
    id: str
    name: str
    description: str = ""
    category: str = "General"  # For organizing presets
    target_groups: list[str] = field(default_factory=list)
    target_fixtures: list[str] = field(default_factory=list)
    color: str = "#ffffff"
    color_name: str = "white"
    intensity: int = 100
    intensity_min: int = 0
    intensity_max: int = 100
    effect_type: str = "static"  # static, pulse, chase, strobe, fade, rainbow, movement, blackout
    speed_bpm: int = 120
    direction: str = "forward"  # forward, reverse, bounce, random
    transition: str = "instant"  # instant, crossfade
    transition_time: float = 0.0
    # New fields for movement, rainbow, and other effects
    cycle_seconds: float = 0
    movement_pattern: str = "none"  # none, circle, pan, tilt, figure8, diagonal, square, random
    rainbow_colors: bool = False  # Enable rainbow color cycling
    pan_min: int = 0
    pan_max: int = 255
    tilt_min: int = 64
    tilt_max: int = 192
    macro_value: int = 0
    color_wheel_value: int = -1  # -1 means use RGB color
    gobo_value: int = 0
    gobo_rotation_value: int = 0
    gobo2_value: int = 0
    gobo2_rotation_value: int = 0
    effect_channel_value: int = -1  # -1 means not set
    position_preset: str = ""  # Name of position preset to apply
    color_palette: list[str] = field(default_factory=list)  # List of hex colors for fixture variety
    fixture_offset: float = 0.25  # 0.0 = all sync, 1.0 = max spread
    # Position cycling settings
    position_cycle_enabled: bool = False
    position_cycle_presets: list[str] = field(default_factory=list)  # List of position preset IDs to cycle
    position_cycle_hold_time: float = 4.0
    position_cycle_speed: int = 0  # Pan/Tilt speed DMX (0 = fastest)
    # Master effect speed multiplier (10-400, where 100 = 1.0x)
    master_speed: int = 100
    # Sub-tab enabled/disabled flags (for REFINE tab)
    color_subtab_enabled: bool = False
    effect_subtab_enabled: bool = False
    speed_subtab_enabled: bool = False
    strobe_subtab_enabled: bool = False
    movement_subtab_enabled: bool = False
    patterns_subtab_enabled: bool = False
    position_subtab_enabled: bool = False
    gobo_subtab_enabled: bool = False
    intensity_subtab_enabled: bool = False
    target_subtab_enabled: bool = False
    # Layer-based effect stack (new system: list of EffectLayer dicts)
    layers: list[dict] = field(default_factory=list)
    
    def to_dict(self) -> dict:
        return {
            'id': self.id,
            'name': self.name,
            'description': self.description,
            'category': self.category,
            'target_groups': self.target_groups,
            'target_fixtures': self.target_fixtures,
            'color': self.color,
            'color_name': self.color_name,
            'intensity': self.intensity,
            'intensity_min': self.intensity_min,
            'intensity_max': self.intensity_max,
            'effect_type': self.effect_type,
            'speed_bpm': self.speed_bpm,
            'direction': self.direction,
            'transition': self.transition,
            'transition_time': self.transition_time,
            'cycle_seconds': self.cycle_seconds,
            'movement_pattern': self.movement_pattern,
            'rainbow_colors': self.rainbow_colors,
            'pan_min': self.pan_min,
            'pan_max': self.pan_max,
            'tilt_min': self.tilt_min,
            'tilt_max': self.tilt_max,
            'macro_value': self.macro_value,
            'color_wheel_value': self.color_wheel_value,
            'gobo_value': self.gobo_value,
            'gobo_rotation_value': self.gobo_rotation_value,
            'gobo2_value': self.gobo2_value,
            'gobo2_rotation_value': self.gobo2_rotation_value,
            'effect_channel_value': self.effect_channel_value,
            'position_preset': self.position_preset,
            'color_palette': self.color_palette,
            'fixture_offset': self.fixture_offset,
            'position_cycle_enabled': self.position_cycle_enabled,
            'position_cycle_presets': self.position_cycle_presets,
            'position_cycle_hold_time': self.position_cycle_hold_time,
            'position_cycle_speed': self.position_cycle_speed,
            'master_speed': self.master_speed,
            'color_subtab_enabled': self.color_subtab_enabled,
            'effect_subtab_enabled': self.effect_subtab_enabled,
            'speed_subtab_enabled': self.speed_subtab_enabled,
            'strobe_subtab_enabled': self.strobe_subtab_enabled,
            'movement_subtab_enabled': self.movement_subtab_enabled,
            'patterns_subtab_enabled': self.patterns_subtab_enabled,
            'position_subtab_enabled': self.position_subtab_enabled,
            'gobo_subtab_enabled': self.gobo_subtab_enabled,
            'intensity_subtab_enabled': self.intensity_subtab_enabled,
            'target_subtab_enabled': self.target_subtab_enabled,
            'layers': self.layers
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'EffectPreset':
        return cls(
            id=data['id'],
            name=data['name'],
            description=data.get('description', ''),
            category=data.get('category', 'General'),
            target_groups=data.get('target_groups', []),
            target_fixtures=data.get('target_fixtures', []),
            color=data.get('color', '#ffffff'),
            color_name=data.get('color_name', 'white'),
            intensity=data.get('intensity', 100),
            intensity_min=data.get('intensity_min', 0),
            intensity_max=data.get('intensity_max', 100),
            effect_type=data.get('effect_type', 'static'),
            speed_bpm=data.get('speed_bpm', 120),
            direction=data.get('direction', 'forward'),
            transition=data.get('transition', 'instant'),
            transition_time=data.get('transition_time', 0.0),
            cycle_seconds=data.get('cycle_seconds', 0),
            movement_pattern=data.get('movement_pattern', 'none'),
            rainbow_colors=data.get('rainbow_colors', False),
            pan_min=data.get('pan_min', 0),
            pan_max=data.get('pan_max', 255),
            tilt_min=data.get('tilt_min', 64),
            tilt_max=data.get('tilt_max', 192),
            macro_value=data.get('macro_value', 0),
            color_wheel_value=data.get('color_wheel_value', -1),
            gobo_value=data.get('gobo_value', 0),
            gobo_rotation_value=data.get('gobo_rotation_value', 0),
            gobo2_value=data.get('gobo2_value', 0),
            gobo2_rotation_value=data.get('gobo2_rotation_value', 0),
            effect_channel_value=data.get('effect_channel_value', -1),
            position_preset=data.get('position_preset', ''),
            color_palette=data.get('color_palette', []),
            fixture_offset=float(data.get('fixture_offset', 0.25)),
            position_cycle_enabled=data.get('position_cycle_enabled', False),
            position_cycle_presets=data.get('position_cycle_presets', []),
            position_cycle_hold_time=data.get('position_cycle_hold_time', 4.0),
            position_cycle_speed=data.get('position_cycle_speed', 0),
            master_speed=data.get('master_speed', 100),
            color_subtab_enabled=data.get('color_subtab_enabled', False),
            effect_subtab_enabled=data.get('effect_subtab_enabled', False),
            speed_subtab_enabled=data.get('speed_subtab_enabled', False),
            strobe_subtab_enabled=data.get('strobe_subtab_enabled', False),
            movement_subtab_enabled=data.get('movement_subtab_enabled', False),
            patterns_subtab_enabled=data.get('patterns_subtab_enabled', False),
            position_subtab_enabled=data.get('position_subtab_enabled', False),
            gobo_subtab_enabled=data.get('gobo_subtab_enabled', False),
            intensity_subtab_enabled=data.get('intensity_subtab_enabled', False),
            target_subtab_enabled=data.get('target_subtab_enabled', False),
            layers=data.get('layers', [])
        )


@dataclass
class FixtureGroup:
    """A group of fixtures for collective control."""
    id: str
    name: str
    fixture_ids: list[str] = field(default_factory=list)
    color: str = "#0078d4"  # Display color
    
    def to_dict(self) -> dict:
        return {
            'id': self.id,
            'name': self.name,
            'fixture_ids': self.fixture_ids,
            'color': self.color
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'FixtureGroup':
        return cls(
            id=data['id'],
            name=data['name'],
            fixture_ids=data.get('fixture_ids', []),
            color=data.get('color', '#0078d4')
        )


@dataclass
class PositionPreset:
    """A saved pan/tilt position preset for moving head fixtures.
    
    fixture_positions maps fixture_id -> {"pan": int, "tilt": int, "dimmer": int, "shutter": int, "color": str}
    Only pan/tilt are required. dimmer (0-255), shutter (0-255), and color (hex string) are optional.
    When used on a position fader, all stored values are interpolated from home to target.
    """
    id: str
    name: str  # Human-readable name (e.g., "Audience", "Stage Floor", "Drummer")
    description: str = ""  # Optional description for AI context
    # fixture_id -> {"pan": int, "tilt": int, "dimmer": int, "shutter": int, "color": "#rrggbb"}
    fixture_positions: dict[str, dict[str, int | str]] = field(default_factory=dict)
    # AI-friendly aliases (e.g., ["crowd", "house", "audience area"])
    aliases: list[str] = field(default_factory=list)
    # Movement speed override (0-255, None = no override, higher = slower movement)
    move_speed: int | None = None
    
    def to_dict(self) -> dict:
        d = {
            'id': self.id,
            'name': self.name,
            'description': self.description,
            'fixture_positions': self.fixture_positions,
            'aliases': self.aliases
        }
        if self.move_speed is not None:
            d['move_speed'] = self.move_speed
        return d
    
    @classmethod
    def from_dict(cls, data: dict) -> 'PositionPreset':
        return cls(
            id=data['id'],
            name=data['name'],
            description=data.get('description', ''),
            fixture_positions=data.get('fixture_positions', {}),
            aliases=data.get('aliases', []),
            move_speed=data.get('move_speed')
        )


@dataclass
class ColorPalette:
    """A saved color palette for fixture variety."""
    id: str
    name: str  # Human-readable name (e.g., "Warm Sunset", "Cool Blues")
    colors: list[str] = field(default_factory=list)  # List of hex colors
    
    def to_dict(self) -> dict:
        return {
            'id': self.id,
            'name': self.name,
            'colors': self.colors
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'ColorPalette':
        return cls(
            id=data['id'],
            name=data['name'],
            colors=data.get('colors', [])
        )


@dataclass
class Shortcut:
    """A shortcut button that sends OSC and/or MIDI messages."""
    id: str
    name: str  # Display label
    color: str = "#c97a50"  # Button color (same as execute tab defaults)
    # OSC configuration (optional)
    osc_enabled: bool = False
    osc_ip: str = "127.0.0.1"
    osc_port: int = 8000
    osc_address: str = "/"
    osc_args: list = field(default_factory=list)  # List of args (int, float, str)
    # MIDI configuration (optional)
    midi_enabled: bool = False
    midi_type: str = "note_on"  # 'note_on', 'note_off', 'cc', 'program_change'
    midi_channel: int = 1  # 1-16
    midi_note: int = 60  # Note number or CC number
    midi_velocity: int = 100  # Velocity or CC value
    midi_duration: float = 0.1  # Duration for note_on (seconds)
    
    def to_dict(self) -> dict:
        return {
            'id': self.id,
            'name': self.name,
            'color': self.color,
            'osc_enabled': self.osc_enabled,
            'osc_ip': self.osc_ip,
            'osc_port': self.osc_port,
            'osc_address': self.osc_address,
            'osc_args': self.osc_args,
            'midi_enabled': self.midi_enabled,
            'midi_type': self.midi_type,
            'midi_channel': self.midi_channel,
            'midi_note': self.midi_note,
            'midi_velocity': self.midi_velocity,
            'midi_duration': self.midi_duration
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'Shortcut':
        return cls(
            id=data['id'],
            name=data['name'],
            color=data.get('color', '#c97a50'),
            osc_enabled=data.get('osc_enabled', False),
            osc_ip=data.get('osc_ip', '127.0.0.1'),
            osc_port=data.get('osc_port', 8000),
            osc_address=data.get('osc_address', '/'),
            osc_args=data.get('osc_args', []),
            midi_enabled=data.get('midi_enabled', False),
            midi_type=data.get('midi_type', 'note_on'),
            midi_channel=data.get('midi_channel', 1),
            midi_note=data.get('midi_note', 60),
            midi_velocity=data.get('midi_velocity', 100),
            midi_duration=data.get('midi_duration', 0.1)
        )


@dataclass
class ShortcutPage:
    """A page of shortcuts (a tab within the Shortcuts tab)."""
    id: str
    name: str  # Tab name
    shortcuts: list[Shortcut] = field(default_factory=list)
    
    def to_dict(self) -> dict:
        return {
            'id': self.id,
            'name': self.name,
            'shortcuts': [s.to_dict() for s in self.shortcuts]
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'ShortcutPage':
        return cls(
            id=data['id'],
            name=data['name'],
            shortcuts=[Shortcut.from_dict(s) for s in data.get('shortcuts', [])]
        )


@dataclass
class ExecutePage:
    """A page of execute presets (a tab within the Execute tab)."""
    id: str
    name: str  # Tab name
    preset_ids: list[str] = field(default_factory=list)  # List of preset IDs on this page
    
    def to_dict(self) -> dict:
        return {
            'id': self.id,
            'name': self.name,
            'preset_ids': self.preset_ids
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'ExecutePage':
        return cls(
            id=data['id'],
            name=data['name'],
            preset_ids=data.get('preset_ids', [])
        )


@dataclass
class FaderConfig:
    """Configuration for a single fader on a fader page."""
    id: str  # Unique identifier for this fader
    name: str = "Fader"
    assigned_preset_id: Optional[str] = None  # Which preset/effect this fader controls
    assigned_preset_type: str = "effect"  # "effect" or "preset"
    value: int = 0  # Current fader value (0-100)
    midi_ccs: list[int] = field(default_factory=list)  # MIDI CCs assigned to this fader (supports multiple)
    
    def to_dict(self) -> dict:
        """Convert to dictionary for JSON serialization."""
        return {
            "id": self.id,
            "name": self.name,
            "assigned_preset_id": self.assigned_preset_id,
            "assigned_preset_type": self.assigned_preset_type,
            "value": self.value,
            "midi_ccs": self.midi_ccs,
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'FaderConfig':
        """Create from dictionary."""
        # Support both old single midi_cc and new midi_ccs list format
        midi_ccs = data.get("midi_ccs", [])
        if not midi_ccs and "midi_cc" in data:
            midi_ccs = [data["midi_cc"]] if data["midi_cc"] else []
        
        return cls(
            id=data.get("id", ""),
            name=data.get("name", "Fader"),
            assigned_preset_id=data.get("assigned_preset_id"),
            assigned_preset_type=data.get("assigned_preset_type", "effect"),
            value=data.get("value", 0),
            midi_ccs=midi_ccs,
        )


@dataclass
class FaderPage:
    """A page containing multiple faders."""
    id: str  # Unique identifier
    name: str = "Page"
    faders: list[FaderConfig] = field(default_factory=list)
    
    def __post_init__(self):
        """Ensure 9 faders exist."""
        while len(self.faders) < 9:
            fader_id = f"{self.id}_fader_{len(self.faders)}"
            self.faders.append(FaderConfig(id=fader_id, name=f"Fader {len(self.faders) + 1}"))

    
    def to_dict(self) -> dict:
        """Convert to dictionary for JSON serialization."""
        return {
            "id": self.id,
            "name": self.name,
            "faders": [f.to_dict() for f in self.faders],
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'FaderPage':
        """Create from dictionary."""
        faders = [FaderConfig.from_dict(f) for f in data.get("faders", [])]
        return cls(
            id=data.get("id", ""),
            name=data.get("name", "Page"),
            faders=faders,
        )


@dataclass
class FadersProject:
    """Container for all fader pages in a project."""
    pages: list[FaderPage] = field(default_factory=list)
    current_page_id: Optional[str] = None
    
    def __post_init__(self):
        """Ensure at least 2 pages exist."""
        if not self.pages:
            page1 = FaderPage(id="page_0", name="Page 1")
            page2 = FaderPage(id="page_1", name="Page 2")
            self.pages = [page1, page2]
            self.current_page_id = page1.id
    
    def get_current_page(self) -> Optional[FaderPage]:
        """Get the currently active page."""
        if self.current_page_id:
            for page in self.pages:
                if page.id == self.current_page_id:
                    return page
        return self.pages[0] if self.pages else None
    
    def add_page(self, name: str = "Page") -> FaderPage:
        """Add a new fader page."""
        page_id = f"page_{len(self.pages)}"
        new_page = FaderPage(id=page_id, name=name)
        self.pages.append(new_page)
        return new_page
    
    def delete_page(self, page_id: str):
        """Delete a fader page."""
        self.pages = [p for p in self.pages if p.id != page_id]
        if self.current_page_id == page_id:
            self.current_page_id = self.pages[0].id if self.pages else None
    
    def to_dict(self) -> dict:
        """Convert to dictionary for JSON serialization."""
        return {
            "pages": [p.to_dict() for p in self.pages],
            "current_page_id": self.current_page_id,
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'FadersProject':
        """Create from dictionary."""
        if not data:
            return cls()
        pages = [FaderPage.from_dict(p) for p in data.get("pages", [])]
        return cls(
            pages=pages,
            current_page_id=data.get("current_page_id"),
        )


# ── Cue system ────────────────────────────────────────────────────────

@dataclass
class CueStep:
    """A single step within a cue — references one preset plus timing overrides."""
    preset_id: str                         # ID of the EffectPreset to fire
    wait_time: float = 0.0                 # Seconds to wait AFTER this step before auto-advancing
    fade_in_time: float = 1.0             # Crossfade-in time in seconds
    fade_out_time: float = 1.0            # Crossfade-out time in seconds
    light_speed: int = 100                 # Speed override for fixture speed channels (0-255 DMX)
    effect_speed: int = 100                # Master speed multiplier for effect BPM (10-400, 100=1x)
    timecode: str = ""                     # SMPTE timecode trigger (HH:MM:SS:FF), empty = disabled
    position_preset_id: str = ""           # Position preset ID to recall with this step
    visualizer_item_id: str = ""           # Visualizer item ID to play with this step

    def to_dict(self) -> dict:
        d = {
            'preset_id': self.preset_id,
            'wait_time': self.wait_time,
            'fade_in_time': self.fade_in_time,
            'fade_out_time': self.fade_out_time,
            'light_speed': self.light_speed,
            'effect_speed': self.effect_speed,
        }
        if self.timecode:
            d['timecode'] = self.timecode
        if self.position_preset_id:
            d['position_preset_id'] = self.position_preset_id
        if self.visualizer_item_id:
            d['visualizer_item_id'] = self.visualizer_item_id
        return d

    @classmethod
    def from_dict(cls, data: dict) -> 'CueStep':
        return cls(
            preset_id=data['preset_id'],
            wait_time=data.get('wait_time', 0.0),
            fade_in_time=data.get('fade_in_time', 1.0),
            fade_out_time=data.get('fade_out_time', 1.0),
            light_speed=data.get('light_speed', 100),
            effect_speed=data.get('effect_speed', 100),
            timecode=data.get('timecode', ''),
            position_preset_id=data.get('position_preset_id', ''),
            visualizer_item_id=data.get('visualizer_item_id', ''),
        )


@dataclass
class CueList:
    """An ordered list of cue steps with transport MIDI bindings."""
    id: str
    name: str = "New Cue List"
    steps: list[CueStep] = field(default_factory=list)
    loop: bool = False                     # Auto-loop when reaching the end

    # MIDI trigger bindings for transport buttons (stored as "type:channel:note/cc")
    midi_play: str = ""
    midi_stop: str = ""
    midi_next: str = ""
    midi_prev: str = ""
    midi_rewind: str = ""

    def to_dict(self) -> dict:
        return {
            'id': self.id,
            'name': self.name,
            'steps': [s.to_dict() for s in self.steps],
            'loop': self.loop,
            'midi_play': self.midi_play,
            'midi_stop': self.midi_stop,
            'midi_next': self.midi_next,
            'midi_prev': self.midi_prev,
            'midi_rewind': self.midi_rewind,
        }

    @classmethod
    def from_dict(cls, data: dict) -> 'CueList':
        return cls(
            id=data['id'],
            name=data.get('name', 'New Cue List'),
            steps=[CueStep.from_dict(s) for s in data.get('steps', [])],
            loop=data.get('loop', False),
            midi_play=data.get('midi_play', ''),
            midi_stop=data.get('midi_stop', ''),
            midi_next=data.get('midi_next', ''),
            midi_prev=data.get('midi_prev', ''),
            midi_rewind=data.get('midi_rewind', ''),
        )


@dataclass
class LightingProject:
    """A complete lighting project."""
    name: str
    universe_count: int = 4
    fixtures: list[PatchedFixture] = field(default_factory=list)
    groups: list[FixtureGroup] = field(default_factory=list)
    presets: list[EffectPreset] = field(default_factory=list)
    position_presets: list[PositionPreset] = field(default_factory=list)  # Pan/tilt position presets
    color_palettes: list[ColorPalette] = field(default_factory=list)  # Saved color palettes
    shortcut_pages: list[ShortcutPage] = field(default_factory=list)  # OSC/MIDI shortcut pages
    execute_pages: list[ExecutePage] = field(default_factory=list)  # Execute preset pages
    faders: FadersProject = field(default_factory=FadersProject)  # Fader pages and configurations
    cue_lists: list[CueList] = field(default_factory=list)  # Cue lists (ordered preset sequences)
    fixture_sequences: list[FixtureSequence] = field(default_factory=list)
    artnet_ip: str = "255.255.255.255"
    artnet_interface: str = "all"  # Network interface IP or "all" for broadcast
    artnet_fps: int = 44
    profiles: dict[str, FixtureProfile] = field(default_factory=dict)  # Shared profile library
    master_intensity: int = 100  # Master dimmer value (0-100%)
    fixture_type_caps: dict[str, float] = field(default_factory=dict)  # profile_name -> brightness cap (0.0-1.0)
    
    def get_profile(self, profile_id: str) -> Optional[FixtureProfile]:
        """Get a shared profile by ID."""
        return self.profiles.get(profile_id)
    
    def add_or_update_profile(self, profile: FixtureProfile):
        """Add or update a profile in the shared library."""
        old_profile = self.profiles.get(profile.profile_id)
        self.profiles[profile.profile_id] = profile
        # Update all fixtures using this profile
        for fixture in self.fixtures:
            if fixture.profile.profile_id == profile.profile_id:
                # If the mode name changed (e.g., "23ch" -> "24ch"), update fixture's mode_name
                if old_profile and fixture.mode_name not in [m.name for m in profile.modes]:
                    # Mode was renamed - try to find the new mode name
                    if profile.modes:
                        fixture.mode_name = profile.modes[0].name
                fixture.profile = profile
    
    def get_fixture_by_id(self, fixture_id: str) -> Optional[PatchedFixture]:
        for f in self.fixtures:
            if f.id == fixture_id:
                return f
        return None
    
    def get_group_by_name(self, name: str) -> Optional[FixtureGroup]:
        """Get a group by name (case-insensitive)."""
        name_lower = name.lower()
        for g in self.groups:
            if g.name.lower() == name_lower:
                return g
        return None
    
    def get_group_by_id(self, group_id: str) -> Optional[FixtureGroup]:
        """Get a group by ID."""
        for g in self.groups:
            if g.id == group_id:
                return g
        return None
    
    def get_preset_by_id(self, preset_id: str) -> Optional[EffectPreset]:
        """Get a preset by ID."""
        for p in self.presets:
            if p.id == preset_id:
                return p
        return None
    
    def get_position_preset_by_id(self, preset_id: str) -> Optional[PositionPreset]:
        """Get a position preset by ID."""
        for p in self.position_presets:
            if p.id == preset_id:
                return p
        return None
    
    def get_position_preset_by_name(self, name: str) -> Optional[PositionPreset]:
        """Get a position preset by name or alias (case-insensitive, fuzzy match)."""
        name_lower = name.lower().strip()
        
        # Try exact name match first
        for p in self.position_presets:
            if p.name.lower() == name_lower:
                return p
        
        # Try alias match
        for p in self.position_presets:
            for alias in p.aliases:
                if alias.lower() == name_lower:
                    return p
        
        # Try partial match in name
        for p in self.position_presets:
            if name_lower in p.name.lower() or p.name.lower() in name_lower:
                return p
        
        # Try partial match in aliases
        for p in self.position_presets:
            for alias in p.aliases:
                if name_lower in alias.lower() or alias.lower() in name_lower:
                    return p
        
        return None
    
    def get_group_names(self) -> list[str]:
        """Get list of all group names."""
        return [g.name for g in self.groups]
    
    def get_ai_context(self) -> dict:
        """Get project context for AI assistant."""
        # Collect fixture info by category with detailed channel info
        categories = {}
        for fixture in self.fixtures:
            cat = fixture.profile.category
            if cat not in categories:
                categories[cat] = {'fixtures': [], 'capabilities': set()}
            
            # Get channel details
            channels = []
            if fixture.mode:
                for ch in fixture.mode.channels:
                    ch_info = {
                        'name': ch.name,
                        'type': ch.type
                    }
                    # Include color wheel colors if defined
                    if ch.type == 'color_wheel' and ch.color_wheel_colors:
                        ch_info['colors'] = [
                            {'name': c['name'], 'value': c['value']} 
                            for c in ch.color_wheel_colors
                        ]
                    # Include effect values if defined
                    if ch.type == 'effect' and ch.effect_values:
                        ch_info['effects'] = [
                            {'name': e['name'], 'value': e['value'], 'value_end': e.get('value_end', e['value'])} 
                            for e in ch.effect_values
                        ]
                    channels.append(ch_info)
                    categories[cat]['capabilities'].add(ch.type)
            
            fixture_info = {
                'name': fixture.label or fixture.profile.name,
                'id': fixture.id,
                'channels': channels,
                'channel_types': [ch.type for ch in (fixture.mode.channels if fixture.mode else [])]
            }
            # Include home position if set
            if fixture.has_home_position:
                fixture_info['home_position'] = {
                    'pan': fixture.home_pan,
                    'tilt': fixture.home_tilt
                }
            
            categories[cat]['fixtures'].append(fixture_info)
        
        # Convert capabilities sets to sorted lists
        for cat in categories:
            categories[cat]['capabilities'] = sorted(list(categories[cat]['capabilities']))
        
        # Get group info
        groups_info = []
        for group in self.groups:
            fixture_names = []
            fixture_categories = set()
            for fid in group.fixture_ids:
                f = self.get_fixture_by_id(fid)
                if f:
                    fixture_names.append(f.label or f.profile.name)
                    fixture_categories.add(f.profile.category)
            groups_info.append({
                'name': group.name,
                'fixtures': fixture_names,
                'categories': sorted(list(fixture_categories))
            })
        
        # Get position preset info for AI
        position_info = []
        for pos in self.position_presets:
            position_info.append({
                'name': pos.name,
                'description': pos.description,
                'aliases': pos.aliases,
                'fixture_count': len(pos.fixture_positions)
            })
        
        # Collect home position summary for moving heads
        moving_heads_with_home = []
        for fixture in self.fixtures:
            if fixture.has_home_position:
                name = fixture.label or fixture.profile.name
                moving_heads_with_home.append({
                    'name': name,
                    'home_pan': fixture.home_pan,
                    'home_tilt': fixture.home_tilt
                })
        
        return {
            'fixture_count': len(self.fixtures),
            'categories': categories,
            'groups': groups_info,
            'group_names': self.get_group_names(),
            'position_presets': position_info,
            'home_positions': moving_heads_with_home
        }
    
    def get_next_address(self, universe: int) -> int:
        """Find the next available address in a universe."""
        used_ranges = []
        for f in self.fixtures:
            if f.universe == universe:
                used_ranges.append((f.address, f.end_address))
        
        if not used_ranges:
            return 1
        
        used_ranges.sort()
        next_addr = 1
        for start, end in used_ranges:
            if next_addr < start:
                return next_addr
            next_addr = end + 1
        
        return next_addr if next_addr <= 512 else -1
    
    def check_address_conflict(self, universe: int, address: int, channel_count: int, 
                               exclude_id: Optional[str] = None) -> Optional[str]:
        """Check if an address range conflicts with existing fixtures.
        Returns the conflicting fixture label/name or None if no conflict."""
        end_addr = address + channel_count - 1
        
        for f in self.fixtures:
            if f.universe != universe:
                continue
            if exclude_id and f.id == exclude_id:
                continue
            
            # Check for overlap
            if not (end_addr < f.address or address > f.end_address):
                return f.label or f.profile.full_name
        
        return None
    
    def to_dict(self) -> dict:
        # Build shared profiles from fixtures
        profiles_dict = {}
        for f in self.fixtures:
            pid = f.profile.profile_id
            if pid not in profiles_dict:
                profiles_dict[pid] = f.profile.to_dict()
        
        # Serialize fixtures with profile references
        fixtures_data = []
        for f in self.fixtures:
            fixture_data = {
                'id': f.id,
                'profile_id': f.profile.profile_id,
                'mode_name': f.mode_name,
                'universe': f.universe,
                'address': f.address,
                'label': f.label,
                'location_x': f.location_x,
                'location_y': f.location_y
            }
            # Include home positions if set
            if f.home_pan is not None:
                fixture_data['home_pan'] = f.home_pan
            if f.home_tilt is not None:
                fixture_data['home_tilt'] = f.home_tilt
            # Beam calibration (only save non-default values)
            if f.pan_offset != 0.0:
                fixture_data['pan_offset'] = f.pan_offset
            if f.pan_invert:
                fixture_data['pan_invert'] = f.pan_invert
            if f.pan_range != 540.0:
                fixture_data['pan_range'] = f.pan_range
            if f.tilt_offset != 0.0:
                fixture_data['tilt_offset'] = f.tilt_offset
            if f.tilt_invert:
                fixture_data['tilt_invert'] = f.tilt_invert
            if f.tilt_range != 270.0:
                fixture_data['tilt_range'] = f.tilt_range
            # Visual size (always save if non-default, for position layout)
            if f.visual_width != 0.1:
                fixture_data['visual_width'] = f.visual_width
            if f.visual_height != 0.05:
                fixture_data['visual_height'] = f.visual_height
            if f.fixture_rotation != 0:
                fixture_data['fixture_rotation'] = f.fixture_rotation
            # Pixel mapping (only save if enabled)
            if f.is_pixel_mapped:
                fixture_data['is_pixel_mapped'] = True
                fixture_data['pixel_rows'] = f.pixel_rows
                fixture_data['pixel_columns'] = f.pixel_columns
                fixture_data['channels_per_pixel'] = f.channels_per_pixel
                fixture_data['pixel_channel_order'] = f.pixel_channel_order
                fixture_data['pixel_channel_offset'] = f.pixel_channel_offset
                fixture_data['pixel_channel_table'] = f.pixel_channel_table
            # Effect exclusion
            if f.exclude_from_effects:
                fixture_data['exclude_from_effects'] = True
            if f.exclude_from_overlay:
                fixture_data['exclude_from_overlay'] = True
            fixtures_data.append(fixture_data)
        
        return {
            'name': self.name,
            'universe_count': self.universe_count,
            'profiles': profiles_dict,  # Shared profile definitions
            'fixtures': fixtures_data,   # Fixtures reference profiles by ID
            'groups': [g.to_dict() for g in self.groups],
            'presets': [p.to_dict() for p in self.presets],
            'position_presets': [p.to_dict() for p in self.position_presets],
            'color_palettes': [p.to_dict() for p in self.color_palettes],
            'shortcut_pages': [p.to_dict() for p in self.shortcut_pages],
            'execute_pages': [p.to_dict() for p in self.execute_pages],
            'faders': self.faders.to_dict(),
            'cue_lists': [c.to_dict() for c in self.cue_lists],
            'fixture_sequences': [s.to_dict() for s in self.fixture_sequences],
            'artnet_ip': self.artnet_ip,
            'artnet_interface': self.artnet_interface,
            'artnet_fps': self.artnet_fps,
            'master_intensity': self.master_intensity,
            'fixture_type_caps': self.fixture_type_caps,
            'visualizer_data': getattr(self, '_visualizer_data', {}),
            'cue_data': getattr(self, '_cue_data', {}),
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'LightingProject':
        # Load shared profiles first
        profiles = {}
        profiles_data = data.get('profiles', {})
        for pid, pdata in profiles_data.items():
            profiles[pid] = FixtureProfile.from_dict(pdata)
        
        # Load fixtures - try new format (profile_id reference) first
        fixtures = []
        for f in data.get('fixtures', []):
            if 'profile_id' in f:
                # New format: reference to shared profile
                profile = profiles.get(f['profile_id'])
                if profile:
                    fixtures.append(PatchedFixture(
                        id=f['id'],
                        profile=profile,
                        mode_name=f['mode_name'],
                        universe=f['universe'],
                        address=f['address'],
                        label=f.get('label', ''),
                        home_pan=f.get('home_pan'),
                        home_tilt=f.get('home_tilt'),
                        location_x=f.get('location_x', 0.5),
                        location_y=f.get('location_y', 0.5),
                        # Beam calibration
                        pan_offset=f.get('pan_offset', 0.0),
                        pan_invert=f.get('pan_invert', False),
                        pan_range=f.get('pan_range', 540.0),
                        tilt_offset=f.get('tilt_offset', 0.0),
                        tilt_invert=f.get('tilt_invert', False),
                        tilt_range=f.get('tilt_range', 270.0),
                        # Visual size
                        visual_width=f.get('visual_width', 0.1),
                        visual_height=f.get('visual_height', 0.05),
                        fixture_rotation=f.get('fixture_rotation', 0),
                        # Pixel mapping
                        is_pixel_mapped=f.get('is_pixel_mapped', False),
                        pixel_rows=f.get('pixel_rows', 1),
                        pixel_columns=f.get('pixel_columns', 1),
                        channels_per_pixel=f.get('channels_per_pixel', 3),
                        pixel_channel_order=f.get('pixel_channel_order', ['red', 'green', 'blue']),
                        pixel_channel_offset=f.get('pixel_channel_offset', 0),
                        pixel_channel_table=f.get('pixel_channel_table', []),
                        exclude_from_effects=f.get('exclude_from_effects', False),
                        exclude_from_overlay=f.get('exclude_from_overlay', False)
                    ))
            elif 'profile' in f:
                # Old format: embedded profile - migrate to shared
                profile = FixtureProfile.from_dict(f['profile'])
                pid = profile.profile_id
                if pid not in profiles:
                    profiles[pid] = profile
                else:
                    # Use existing shared profile
                    profile = profiles[pid]
                fixtures.append(PatchedFixture(
                    id=f['id'],
                    profile=profile,
                    mode_name=f['mode_name'],
                    universe=f['universe'],
                    address=f['address'],
                    label=f.get('label', ''),
                    home_pan=f.get('home_pan'),
                    home_tilt=f.get('home_tilt'),
                    location_x=f.get('location_x', 0.5),
                    location_y=f.get('location_y', 0.5),
                    # Beam calibration
                    pan_offset=f.get('pan_offset', 0.0),
                    pan_invert=f.get('pan_invert', False),
                    pan_range=f.get('pan_range', 540.0),
                    tilt_offset=f.get('tilt_offset', 0.0),
                    tilt_invert=f.get('tilt_invert', False),
                    tilt_range=f.get('tilt_range', 270.0),
                    # Visual size
                    visual_width=f.get('visual_width', 0.1),
                    visual_height=f.get('visual_height', 0.05),
                    fixture_rotation=f.get('fixture_rotation', 0),
                    # Pixel mapping
                    is_pixel_mapped=f.get('is_pixel_mapped', False),
                    pixel_rows=f.get('pixel_rows', 1),
                    pixel_columns=f.get('pixel_columns', 1),
                    channels_per_pixel=f.get('channels_per_pixel', 3),
                    pixel_channel_order=f.get('pixel_channel_order', ['red', 'green', 'blue']),
                    pixel_channel_offset=f.get('pixel_channel_offset', 0),
                    pixel_channel_table=f.get('pixel_channel_table', []),
                    exclude_from_effects=f.get('exclude_from_effects', False),
                    exclude_from_overlay=f.get('exclude_from_overlay', False)
                ))
        
        project = cls(
            name=data['name'],
            universe_count=data.get('universe_count', 4),
            fixtures=fixtures,
            groups=[FixtureGroup.from_dict(g) for g in data.get('groups', [])],
            presets=[EffectPreset.from_dict(p) for p in data.get('presets', [])],
            position_presets=[PositionPreset.from_dict(p) for p in data.get('position_presets', [])],
            color_palettes=[ColorPalette.from_dict(p) for p in data.get('color_palettes', [])],
            shortcut_pages=[ShortcutPage.from_dict(p) for p in data.get('shortcut_pages', [])],
            execute_pages=[ExecutePage.from_dict(p) for p in data.get('execute_pages', [])],
            faders=FadersProject.from_dict(data.get('faders', {})),
            cue_lists=[CueList.from_dict(c) for c in data.get('cue_lists', [])],
            fixture_sequences=[
                FixtureSequence.from_dict(s)
                for s in data.get('fixture_sequences', [])
            ],
            artnet_ip=data.get('artnet_ip', '255.255.255.255'),
            artnet_interface=data.get('artnet_interface', 'all'),
            artnet_fps=data.get('artnet_fps', 44),
            profiles=profiles,
            master_intensity=data.get('master_intensity', 100),
            fixture_type_caps=data.get('fixture_type_caps', {})
        )
        # Store visualizer data as runtime attribute (not a dataclass field)
        project._visualizer_data = data.get('visualizer_data', {})
        # Store cue data as runtime attribute
        project._cue_data = data.get('cue_data', {})
        return project
    
    def save(self, filepath: str):
        """Save project to JSON file."""
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(self.to_dict(), f, indent=2)
    
    @classmethod
    def load(cls, filepath: str) -> 'LightingProject':
        """Load project from JSON file."""
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
        return cls.from_dict(data)


# Built-in fixture profiles for quick testing
BUILTIN_FIXTURES = [
    FixtureProfile(
        manufacturer="Generic",
        name="Dimmer",
        category="Dimmer",
        modes=[FixtureMode(name="1ch", channels=[
            FixtureChannel(name="Dimmer", type="dimmer")
        ])],
        is_custom=False
    ),
    FixtureProfile(
        manufacturer="Generic",
        name="RGB Par",
        category="Par",
        modes=[
            FixtureMode(name="3ch", channels=[
                FixtureChannel(name="Red", type="red"),
                FixtureChannel(name="Green", type="green"),
                FixtureChannel(name="Blue", type="blue"),
            ]),
            FixtureMode(name="4ch", channels=[
                FixtureChannel(name="Dimmer", type="dimmer"),
                FixtureChannel(name="Red", type="red"),
                FixtureChannel(name="Green", type="green"),
                FixtureChannel(name="Blue", type="blue"),
            ]),
        ],
        is_custom=False
    ),
    FixtureProfile(
        manufacturer="Generic",
        name="RGBW Par",
        category="Par",
        modes=[
            FixtureMode(name="4ch", channels=[
                FixtureChannel(name="Red", type="red"),
                FixtureChannel(name="Green", type="green"),
                FixtureChannel(name="Blue", type="blue"),
                FixtureChannel(name="White", type="white"),
            ]),
            FixtureMode(name="5ch", channels=[
                FixtureChannel(name="Dimmer", type="dimmer"),
                FixtureChannel(name="Red", type="red"),
                FixtureChannel(name="Green", type="green"),
                FixtureChannel(name="Blue", type="blue"),
                FixtureChannel(name="White", type="white"),
            ]),
        ],
        is_custom=False
    ),
    FixtureProfile(
        manufacturer="Generic",
        name="Moving Head Spot",
        category="Moving Head",
        modes=[
            FixtureMode(name="16ch", channels=[
                FixtureChannel(name="Pan", type="pan"),
                FixtureChannel(name="Pan Fine", type="pan_fine"),
                FixtureChannel(name="Tilt", type="tilt"),
                FixtureChannel(name="Tilt Fine", type="tilt_fine"),
                FixtureChannel(name="Speed", type="speed"),
                FixtureChannel(name="Dimmer", type="dimmer"),
                FixtureChannel(name="Strobe", type="strobe"),
                FixtureChannel(name="Red", type="red"),
                FixtureChannel(name="Green", type="green"),
                FixtureChannel(name="Blue", type="blue"),
                FixtureChannel(name="White", type="white"),
                FixtureChannel(name="Color Wheel", type="color_wheel"),
                FixtureChannel(name="Gobo", type="gobo"),
                FixtureChannel(name="Gobo Rotation", type="gobo_rotation"),
                FixtureChannel(name="Focus", type="focus"),
                FixtureChannel(name="Prism", type="prism"),
            ]),
        ],
        is_custom=False
    ),
]
