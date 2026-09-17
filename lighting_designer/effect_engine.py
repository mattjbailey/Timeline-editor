"""
Effect Engine for Lighting Designer
Executes lighting effects and outputs DMX via Art-Net.
"""

import time
import math
import colorsys
import logging
from contextlib import nullcontext
from dataclasses import dataclass, field
from typing import Optional, Callable
from threading import Thread, Event, local as _ThreadLocal
from enum import Enum

# Duration (seconds) over which moving heads smoothly ramp from their current
# position into the first target position of a new movement pattern / position
# cycle.  This prevents the harsh "snap" that happens when an effect jumps a
# fixture from its home (or previous) position straight to wherever the new
# pattern starts.
MOVEMENT_RAMP_IN_SECONDS = 2.0

# Set up logging to same file as gui
import os
_log_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lighting_designer_debug.log')
logger = logging.getLogger(__name__)


@dataclass
class EffectParameters:
    """Parameters for an effect - imported from ai_client but duplicated for standalone use."""
    target_groups: list[str] = field(default_factory=list)
    target_fixtures: list[str] = field(default_factory=list)
    color: str = "#ffffff"
    color_name: str = "white"
    intensity: int = 100
    intensity_min: int = 0
    intensity_max: int = 100
    effect_type: str = "static"
    speed_bpm: int = 120
    direction: str = "forward"
    transition: str = "instant"
    transition_time: float = 0.0
    description: str = ""
    # Moving head specific
    pan_min: int = 0
    pan_max: int = 255
    tilt_min: int = 64
    tilt_max: int = 192
    movement_pattern: str = "none"  # none, circle, figure8, sweep, nod, random
    cycle_seconds: float = 0.0  # Override BPM with explicit cycle time (0 = use BPM)
    # Macro/type channel
    macro_value: int = 0  # 0=off, or specific macro value (1-255)
    # Color wheel specific
    color_wheel_value: int = -1  # DMX value for color wheel (-1 = not set, use color instead)
    # Effect channel specific
    effect_channel_value: int = -1  # DMX value for effect channel (-1 = not set)
    # Gobo channel
    gobo_value: int = 0  # DMX value for gobo channel (0 = open/no gobo)
    gobo_rotation_value: int = 0  # DMX value for gobo rotation (0 = no rotation)
    gobo2_value: int = 0  # DMX value for second gobo wheel (0 = open/no gobo)
    gobo2_rotation_value: int = 0  # DMX value for second gobo rotation (0 = no rotation)
    # Position preset name
    position_preset: str = ""  # Name of position preset to apply
    # Color palette for variety
    color_palette: list = field(default_factory=list)  # List of hex colors for multi-color looks
    # Rainbow effect
    rainbow_colors: bool = False  # Enable rainbow color cycling
    # Position cycle - list of position preset IDs to cycle through (empty = all presets)
    position_cycle_presets: list = field(default_factory=list)
    # Position cycling as independent feature (works with any effect type)
    position_cycle_enabled: bool = False  # Enable position cycling overlay
    position_cycle_hold_time: float = 4.0  # Seconds to hold each position
    position_cycle_speed: int = 0  # Pan/Tilt speed DMX (0 = fastest on most fixtures)
    # Fixture offset for position-based movement effects (0.0 = all sync, 1.0 = max spread)
    fixture_offset: float = 0.25
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
    # Flag to reset moving heads to home when no movement pattern (used when loading presets)
    reset_to_home: bool = False
    # Master effect speed multiplier (10-400, where 100 = 1.0x)
    master_speed: int = 100
    # Fixture-specific DMX channel overrides (-1 = not set / auto)
    prism_value: int = 0       # 0 = off, >0 = prism engaged (fixture-specific DMX value)
    prism_rotation: int = 0    # Prism rotation speed/direction (0 = no rotation)
    prism2_value: int = 0      # Second prism wheel (0 = off)
    prism2_rotation: int = 0   # Second prism rotation (0 = no rotation)
    focus_value: int = -1      # Focus channel (-1 = not set)
    zoom_value: int = -1       # Zoom channel (-1 = not set)
    frost_value: int = 0       # Frost channel (0 = no frost)
    shutter_value: int = -1    # Shutter override (-1 = auto-open)
    # Dimmer effect mode for the dimmer layer type
    dimmer_effect: str = "on"  # on, fade, random_fade, odd_even, left_right, right_left, top_down, bottom_up, center_out, edges_in, sparkle, strobe_fade, build_up, knockdown, wave, checkerboard
    # Layer type for channel ownership filtering (empty = no filter, write all channels)
    layer_type: str = ""  # color, movement, intensity, gobo, strobe, prism, optics, fx_channel, effect, dimmer, other, ""
    # Uncategorized channel values for "other" layer type
    other_channel_values: dict = None
    # Layer-stack precedence for overlapping non-intensity channels.
    # Lower = higher priority (top of the layer list wins).  Default is a
    # large sentinel so non-layer effects (cues, faders) keep LTP behavior.
    stack_order: int = 1_000_000
    
    @classmethod
    def from_dict(cls, data: dict) -> "EffectParameters":
        """
        Factory method to create EffectParameters from a dictionary.
        
        This provides a single source of truth for dict-to-EffectParameters conversion,
        ensuring consistent behavior across Timeline Editor, Player, and any future consumers.
        
        Args:
            data: Dictionary containing effect parameters (typically from effect_data snapshot)
            
        Returns:
            EffectParameters instance with values from dict, using dataclass defaults for missing keys
        """
        return cls(
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
            description=data.get('description', ''),
            pan_min=data.get('pan_min', 0),
            pan_max=data.get('pan_max', 255),
            tilt_min=data.get('tilt_min', 64),
            tilt_max=data.get('tilt_max', 192),
            movement_pattern=data.get('movement_pattern', 'none'),
            cycle_seconds=data.get('cycle_seconds', 0.0),
            macro_value=data.get('macro_value', 0),
            color_wheel_value=data.get('color_wheel_value', -1),
            effect_channel_value=data.get('effect_channel_value', -1),
            gobo_value=data.get('gobo_value', 0),
            gobo_rotation_value=data.get('gobo_rotation_value', 0),
            gobo2_value=data.get('gobo2_value', 0),
            gobo2_rotation_value=data.get('gobo2_rotation_value', 0),
            position_preset=data.get('position_preset', ''),
            color_palette=data.get('color_palette', []),
            rainbow_colors=data.get('rainbow_colors', False),
            position_cycle_presets=data.get('position_cycle_presets', []),
            position_cycle_enabled=data.get('position_cycle_enabled', False),
            position_cycle_hold_time=data.get('position_cycle_hold_time', 4.0),
            position_cycle_speed=data.get('position_cycle_speed', 0),
            fixture_offset=data.get('fixture_offset', 0.25),
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
            reset_to_home=data.get('reset_to_home', False),
            master_speed=data.get('master_speed', 100),
            prism_value=data.get('prism_value', 0),
            prism_rotation=data.get('prism_rotation', 0),
            prism2_value=data.get('prism2_value', 0),
            prism2_rotation=data.get('prism2_rotation', 0),
            focus_value=data.get('focus_value', -1),
            zoom_value=data.get('zoom_value', -1),
            frost_value=data.get('frost_value', 0),
            shutter_value=data.get('shutter_value', -1),
            dimmer_effect=data.get('dimmer_effect', 'on'),
            layer_type=data.get('layer_type', ''),
            other_channel_values=data.get('other_channel_values'),
        )


def hex_to_rgb(hex_color: str) -> tuple[int, int, int]:
    """Convert hex color to RGB tuple (0-255)."""
    hex_color = hex_color.lstrip('#')
    if len(hex_color) == 3:
        hex_color = ''.join(c*2 for c in hex_color)
    return tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4))


def color_distance(rgb1: tuple, rgb2: tuple) -> float:
    """Calculate color distance between two RGB tuples using weighted Euclidean distance."""
    # Use weighted distance - human eye is more sensitive to green, then red, then blue
    r1, g1, b1 = rgb1
    r2, g2, b2 = rgb2
    return math.sqrt(
        2 * (r1 - r2) ** 2 +
        4 * (g1 - g2) ** 2 +
        3 * (b1 - b2) ** 2
    )


def _rgb_hue(r: int, g: int, b: int) -> float:
    """Return hue in degrees (0-360) or -1.0 for achromatic."""
    hi = max(r, g, b)
    lo = min(r, g, b)
    c = hi - lo
    if c == 0 or hi == 0:
        return -1.0
    if hi == r:
        h = ((g - b) / c) % 6.0
    elif hi == g:
        h = (b - r) / c + 2.0
    else:
        h = (r - g) / c + 4.0
    return h * 60.0


def find_closest_color_wheel_value(target_color: str, color_wheel_colors: list) -> tuple[int, str]:
    """
    Find the closest color wheel value for a given target color using
    hue-based matching.  Falls back to RGB distance for achromatic targets.
    
    Args:
        target_color: Hex color string (e.g., "#0000ff")
        color_wheel_colors: List of color wheel entries [{name, value, color}, ...]
        
    Returns:
        Tuple of (dmx_value, color_name) for the closest match
    """
    if not color_wheel_colors:
        return (0, "white")
    
    tr, tg, tb = hex_to_rgb(target_color)
    t_hue = _rgb_hue(tr, tg, tb)
    
    best_match = color_wheel_colors[0]
    best_dist = float('inf')
    
    for wc in color_wheel_colors:
        wr, wg, wb = hex_to_rgb(wc.get('color', '#ffffff'))
        w_hue = _rgb_hue(wr, wg, wb)
        
        # If target is achromatic or wheel entry is achromatic, use RGB distance
        if t_hue < 0 or w_hue < 0:
            d = color_distance((tr, tg, tb), (wr, wg, wb))
        else:
            # Circular hue distance (0-180)
            d = abs(t_hue - w_hue)
            if d > 180.0:
                d = 360.0 - d
        
        if d < best_dist:
            best_dist = d
            best_match = wc
    
    return (best_match.get('value', 0), best_match.get('name', 'unknown'))


def rgb_to_hex(r: int, g: int, b: int) -> str:
    """Convert RGB to hex color."""
    return f"#{r:02x}{g:02x}{b:02x}"


def interpolate_color(color1: str, color2: str, t: float) -> str:
    """Interpolate between two hex colors. t=0 gives color1, t=1 gives color2."""
    r1, g1, b1 = hex_to_rgb(color1)
    r2, g2, b2 = hex_to_rgb(color2)
    r = int(r1 + (r2 - r1) * t)
    g = int(g1 + (g2 - g1) * t)
    b = int(b1 + (b2 - b1) * t)
    return rgb_to_hex(r, g, b)


def get_rainbow_color(position: float) -> str:
    """Get a rainbow color at position (0.0 - 1.0)."""
    r, g, b = colorsys.hsv_to_rgb(position, 1.0, 1.0)
    return rgb_to_hex(int(r * 255), int(g * 255), int(b * 255))


# ============ Pixel Mapping Helpers ============

def get_pixel_canvas_positions(fixture) -> list[dict]:
    """
    Calculate canvas positions for each pixel in a pixel-mapped fixture.
    
    Args:
        fixture: PatchedFixture with pixel mapping configured
        
    Returns:
        List of dicts with pixel info including canvas position:
        [{'pixel_num': 1, 'row': 1, 'col': 1, 'canvas_x': 0.1, 'canvas_y': 0.2, 
          'red': 0, 'green': 1, 'blue': 2}, ...]
    """
    profile = fixture.profile
    if not profile.is_pixel_fixture or not profile.pixel_channel_table:
        return []
    
    results = []
    rows = max(1, profile.pixel_rows)
    cols = max(1, profile.pixel_columns)
    
    # Get fixture's visual bounds on canvas
    fx = getattr(fixture, 'location_x', 0.5)
    fy = getattr(fixture, 'location_y', 0.5)
    fw = getattr(fixture, 'visual_width', 0.1)
    fh = getattr(fixture, 'visual_height', 0.05)
    
    # DEBUG: Log pixel mapping info once per fixture
    if not hasattr(get_pixel_canvas_positions, '_debug_shown'):
        get_pixel_canvas_positions._debug_shown = set()
    
    fixture_key = (fixture.id, fixture.label)
    if fixture_key not in get_pixel_canvas_positions._debug_shown:
        get_pixel_canvas_positions._debug_shown.add(fixture_key)
        print(f"[PixelMapping] Fixture: {fixture.label}")
        print(f"  - Profile: {profile.name}")
        print(f"  - is_pixel_fixture: {profile.is_pixel_fixture}")
        print(f"  - pixel_rows: {rows}, pixel_columns: {cols}")
        print(f"  - pixel_channel_table entries: {len(profile.pixel_channel_table)}")
        print(f"  - Fixture location: ({fx}, {fy})")
        print(f"  - Fixture visual size: {fw} x {fh}")
    
    for pixel_data in profile.pixel_channel_table:
        row = pixel_data.get('row', 1)
        col = pixel_data.get('col', 1)
        pixel_num = pixel_data.get('pixel_num', 1)
        
        # Calculate normalized position within the fixture (0.0 to 1.0)
        # Pixel row 1, col 1 is top-left
        norm_x = (col - 0.5) / cols  # Center of pixel cell
        norm_y = (row - 0.5) / rows
        
        # Convert to canvas position
        canvas_x = fx + norm_x * fw
        canvas_y = fy + norm_y * fh
        
        pixel_info = {
            'pixel_num': pixel_num,
            'row': row,
            'col': col,
            'canvas_x': canvas_x,
            'canvas_y': canvas_y,
            'fixture': fixture,
            # Copy channel mappings
            **{k: v for k, v in pixel_data.items() if k not in ('row', 'col', 'pixel_num')}
        }
        results.append(pixel_info)
    
    return results


def get_all_pixel_positions(fixtures: list) -> list[dict]:
    """
    Get all pixel positions across all pixel-mapped fixtures, sorted by canvas X.
    
    Args:
        fixtures: List of PatchedFixture objects
        
    Returns:
        List of pixel position dicts sorted by canvas_x, then canvas_y
    """
    all_pixels = []
    for fixture in fixtures:
        if fixture.profile.is_pixel_fixture:
            all_pixels.extend(get_pixel_canvas_positions(fixture))
    
    # Sort by X position (left to right), then Y position (top to bottom)
    all_pixels.sort(key=lambda p: (p['canvas_x'], p['canvas_y']))
    return all_pixels


def apply_color_to_pixel(buffer: dict, pixel_info: dict, r: int, g: int, b: int, 
                         intensity_scale: float = 1.0, white: int = 0):
    """
    Apply a color to a pixel's DMX channels in the buffer.
    Skips any channels that are typed as 'strobe' in the fixture mode.
    
    Args:
        buffer: DMX buffer dict {(universe, addr): (value, ch_type)}
        pixel_info: Pixel dict with channel offsets and fixture reference
        r, g, b: RGB values 0-255
        intensity_scale: 0.0 to 1.0 intensity multiplier
        white: White channel value 0-255 (for RGBW pixels)
    """
    fixture = pixel_info.get('fixture')
    if not fixture:
        return
    
    uni = fixture.universe
    base_addr = fixture.address
    
    # Get mode channels to check channel types
    mode = fixture.profile.get_mode(fixture.mode_name)
    mode_channels = mode.channels if mode else []
    
    # Channel types that are safe for pixel effects to write to
    PIXEL_SAFE_TYPES = {'dimmer', 'intensity', 'red', 'green', 'blue', 'white',
                       'warm_white', 'cool_white', 'amber', 'uv', 'master', 'master dimmer'}
    
    def is_safe_pixel_channel(channel_offset: int) -> bool:
        """Check if a channel offset is safe to write pixel data to."""
        if channel_offset < len(mode_channels):
            return mode_channels[channel_offset].type.lower() in PIXEL_SAFE_TYPES
        return True
    
    # Apply color channels with intensity scaling (only if channel type is safe)
    if 'red' in pixel_info and is_safe_pixel_channel(pixel_info['red']):
        addr = base_addr + pixel_info['red']
        buffer[(uni, addr)] = (int(r * intensity_scale), 'red')
    
    if 'green' in pixel_info and is_safe_pixel_channel(pixel_info['green']):
        addr = base_addr + pixel_info['green']
        buffer[(uni, addr)] = (int(g * intensity_scale), 'green')
    
    if 'blue' in pixel_info and is_safe_pixel_channel(pixel_info['blue']):
        addr = base_addr + pixel_info['blue']
        buffer[(uni, addr)] = (int(b * intensity_scale), 'blue')
    
    if 'white' in pixel_info and is_safe_pixel_channel(pixel_info['white']):
        addr = base_addr + pixel_info['white']
        buffer[(uni, addr)] = (int(white * intensity_scale), 'white')
    
    # Only write dimmer if the actual mode channel at this offset is a dimmer type
    if 'dimmer' in pixel_info and is_safe_pixel_channel(pixel_info['dimmer']):
        addr = base_addr + pixel_info['dimmer']
        buffer[(uni, addr)] = (int(255 * intensity_scale), 'dimmer')


def set_pixel_fixture_master_dimmers(buffer: dict, fixtures: list, intensity_per_fixture: dict = None):
    """
    Set fixture-level master dimmers in the buffer for pixel fixtures.
    
    This ensures that the fixture's master dimmer (separate from per-pixel dimmers)
    is set appropriately so pixels can actually light up. If intensity_per_fixture
    is provided, use that value for each fixture's master dimmer; otherwise set to 255.
    
    Also turns OFF strobe channels which should not be active during pixel effects.
    
    Args:
        buffer: DMX buffer dict {(universe, addr): (value, ch_type)}
        fixtures: List of PatchedFixture objects
        intensity_per_fixture: Optional dict {fixture_id: max_intensity_0_255} to set
                               master dimmer based on max pixel brightness
    """
    for fixture in fixtures:
        if not fixture.profile.is_pixel_fixture:
            continue
            
        mode = fixture.profile.get_mode(fixture.mode_name)
        if not mode:
            continue
            
        pixel_table = fixture.profile.pixel_channel_table or []
        uni = fixture.universe
        base_addr = fixture.address
        
        # Determine master dimmer value for this fixture
        if intensity_per_fixture and fixture.id in intensity_per_fixture:
            master_value = intensity_per_fixture[fixture.id]
        else:
            master_value = 255
        
        for i, ch in enumerate(mode.channels):
            ch_type = ch.type.lower()
            addr = base_addr + i
            
            # Turn OFF strobe channels - they should not be active during pixel effects
            if ch_type == 'strobe':
                buffer[(uni, addr)] = (0, 'strobe')
                continue
            
            # On/Off channels - set to on_value when any pixel is active
            if ch_type == 'on_off':
                if master_value > 0:
                    buffer[(uni, addr)] = (getattr(ch, 'on_value', 255), 'on_off')
                else:
                    buffer[(uni, addr)] = (getattr(ch, 'off_value', 0), 'on_off')
                continue
            
            # Shutter channels - open when active
            if ch_type == 'shutter':
                buffer[(uni, addr)] = (255 if master_value > 0 else 0, 'shutter')
                continue
            
            # Look for fixture-level master dimmer (not a per-pixel dimmer)
            if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                # Check if this is a per-pixel dimmer
                is_pixel_dimmer = any(p.get('dimmer') == i for p in pixel_table)
                if not is_pixel_dimmer:
                    # This is a fixture-level master dimmer
                    buffer[(uni, addr)] = (master_value, 'master dimmer')


# ============ Strobe Pixel Mapping Helpers ============

def get_strobe_canvas_positions(fixture, min_strobe_count: int = 2) -> list[dict]:
    """
    Find strobe-type channels in a fixture and map them to canvas positions.
    
    Strobe channels are individual intensity channels (type='strobe') that can be
    pixel-mapped separately from RGB pixels. This searches the fixture's mode
    channels for strobe types and assigns them positions based on their order.
    
    If the fixture has a pixel_channel_table, use that for positioning.
    Otherwise, arrange strobes vertically within the fixture bounds.
    
    Only returns strobes from fixtures that have at least min_strobe_count strobe
    channels, to filter out single strobe speed channels on moving heads/spots.
    
    Args:
        fixture: PatchedFixture with potential strobe channels
        min_strobe_count: Minimum number of strobe channels required (default 2)
                          to be considered a pixel-mappable strobe fixture
        
    Returns:
        List of dicts with strobe info including canvas position:
        [{'strobe_num': 1, 'channel_offset': 0, 'canvas_x': 0.1, 'canvas_y': 0.2, 
          'fixture': fixture}, ...]
    """
    mode = fixture.profile.get_mode(fixture.mode_name)
    if not mode:
        return []
    
    # Find all strobe-type channels
    strobe_channels = []
    for i, channel in enumerate(mode.channels):
        if channel.type.lower() == 'strobe':
            strobe_channels.append({
                'channel_offset': i,
                'name': channel.name
            })
    
    # Only include fixtures with multiple strobe channels (pixel-mappable strobes)
    # Single strobe channels are usually strobe speed controls, not pixel-mappable
    if len(strobe_channels) < min_strobe_count:
        return []
    
    results = []
    num_strobes = len(strobe_channels)
    
    # Get fixture's visual bounds on canvas
    fx = getattr(fixture, 'location_x', 0.5)
    fy = getattr(fixture, 'location_y', 0.5)
    fw = getattr(fixture, 'visual_width', 0.1)
    fh = getattr(fixture, 'visual_height', 0.05)
    
    profile = fixture.profile
    pixel_table = profile.pixel_channel_table if profile else []
    rows = max(1, getattr(profile, 'pixel_rows', 1))
    cols = max(1, getattr(profile, 'pixel_columns', 1))
    
    # If we have a pixel_channel_table with matching count, use it for positioning
    if pixel_table and len(pixel_table) == num_strobes:
        for idx, strobe_data in enumerate(strobe_channels):
            pixel_entry = pixel_table[idx]
            row = pixel_entry.get('row', 1)
            col = pixel_entry.get('col', 1)
            
            # Calculate normalized position within the fixture
            norm_x = (col - 0.5) / cols
            norm_y = (row - 0.5) / rows
            
            canvas_x = fx + norm_x * fw
            canvas_y = fy + norm_y * fh
            
            strobe_info = {
                'strobe_num': idx + 1,
                'channel_offset': strobe_data['channel_offset'],
                'name': strobe_data['name'],
                'canvas_x': canvas_x,
                'canvas_y': canvas_y,
                'fixture': fixture,
                'row': row,
                'col': col,
            }
            results.append(strobe_info)
    else:
        # No pixel table or count mismatch - arrange strobes vertically
        for idx, strobe_data in enumerate(strobe_channels):
            # Distribute strobes evenly along the fixture height
            norm_y = (idx + 0.5) / num_strobes
            canvas_x = fx + fw / 2  # Center horizontally
            canvas_y = fy + norm_y * fh
            
            strobe_info = {
                'strobe_num': idx + 1,
                'channel_offset': strobe_data['channel_offset'],
                'name': strobe_data['name'],
                'canvas_x': canvas_x,
                'canvas_y': canvas_y,
                'fixture': fixture,
            }
            results.append(strobe_info)
    
    return results


def get_all_strobe_positions(fixtures: list) -> list[dict]:
    """
    Get all strobe channel positions across all fixtures, sorted by canvas position.
    
    Args:
        fixtures: List of PatchedFixture objects
        
    Returns:
        List of strobe position dicts sorted by canvas_y (top to bottom), then canvas_x
    """
    all_strobes = []
    for fixture in fixtures:
        all_strobes.extend(get_strobe_canvas_positions(fixture))
    
    # Sort by Y position (top to bottom), then X position (left to right)
    # This makes vertical arrangements (like strobe bars) chase top-to-bottom
    all_strobes.sort(key=lambda s: (s['canvas_y'], s['canvas_x']))
    return all_strobes


def apply_intensity_to_strobe(buffer: dict, strobe_info: dict, intensity: int):
    """
    Apply an intensity value to a strobe channel in the buffer.
    
    Args:
        buffer: DMX buffer dict {(universe, addr): (value, ch_type)}
        strobe_info: Strobe dict with channel_offset and fixture reference
        intensity: 0-255 intensity value
    """
    fixture = strobe_info.get('fixture')
    if not fixture:
        return
    
    uni = fixture.universe
    addr = fixture.address + strobe_info['channel_offset']
    buffer[(uni, addr)] = (int(intensity), 'strobe')


def create_effect_engine(artnet, project, on_effect_state_change: Optional[Callable] = None) -> 'EffectEngine':
    """Factory function to create an EffectEngine instance."""
    return EffectEngine(artnet, project, on_effect_state_change)


class ActiveEffect:
    """Represents a single active effect with its own state and fader level."""
    
    def __init__(self, preset_id: str, effect: EffectParameters, fader_level: float = 1.0,
                 fade_in_time: float = 0.3, fade_out_time: float = 0.0, 
                 effect_duration: float = 0.0, reverse: bool = False):
        self.preset_id = preset_id
        self.effect = effect
        self.fader_level = fader_level  # 0.0 to 1.0
        self.thread: Optional[Thread] = None
        self.stop_event = Event()
        self.start_time = time.time()
        self.dmx_buffer: dict = {}  # {(universe, channel): value} - this effect's output
        self.fade_in_progress = 0.0  # 0.0 to 1.0 - fade-in multiplier for smooth transitions
        self.fade_in_duration = fade_in_time if fade_in_time > 0 else 0.3  # seconds - how long to fade in
        self.fade_out_duration = fade_out_time  # seconds - how long to fade out at end
        self.effect_duration = effect_duration  # total effect duration (0 = infinite)
        self.reverse = reverse  # reverse animation direction


class EffectEngine:
    """Engine to run lighting effects on fixtures."""

    # Map of pixel-canvas effect_type keys → _apply_geo_* method names.
    # Used by _buffer_geo_adapter to route geo effects through the HTP buffer.
    _GEO_EFFECT_MAP = {
        'pixel_clock':          '_apply_pixel_clock',
        'geo_hscan':            '_apply_geo_hscan',
        'geo_vscan':            '_apply_geo_vscan',
        'geo_expand_circle':    '_apply_geo_expand_circle',
        'geo_expand_box':       '_apply_geo_expand_box',
        'geo_diagonal':         '_apply_geo_diagonal',
        'geo_ball':             '_apply_geo_ball',
        'geo_multiball':        '_apply_geo_multiball',
        'geo_bounce_line':      '_apply_geo_bounce_line',
        'geo_pong':             '_apply_geo_pong',
        'geo_plasma':           '_apply_geo_plasma',
        'geo_checker':          '_apply_geo_checker',
        'geo_stripes':          '_apply_geo_stripes',
        'geo_matrix':           '_apply_geo_matrix',
        'geo_sparkle':          '_apply_geo_sparkle',
        'geo_stars':            '_apply_geo_stars',
        'geo_fireworks':        '_apply_geo_fireworks',
        'geo_confetti':         '_apply_geo_confetti',
        'geo_flying_stars':     '_apply_geo_flying_stars',
        'geo_comet':            '_apply_geo_comet',
        'geo_spiral':           '_apply_geo_spiral',
        'geo_vortex':           '_apply_geo_vortex',
        'geo_heartbeat':        '_apply_geo_heartbeat',
        'geo_lightning':        '_apply_geo_lightning',
        'geo_wave':             '_apply_geo_wave',
        'geo_dna':              '_apply_geo_dna',
        'geo_radar':            '_apply_geo_radar',
        'geo_crosshair':        '_apply_geo_crosshair',
        'geo_gradient_sweep':   '_apply_geo_gradient_sweep',
        'geo_gradient_vertical':'_apply_geo_gradient_vertical',
        'geo_gradient_radial':  '_apply_geo_gradient_radial',
        'geo_aurora':           '_apply_geo_aurora',
        'geo_lava':             '_apply_geo_lava',
        'geo_breathing':        '_apply_geo_breathing',
        'geo_ocean_waves':      '_apply_geo_ocean_waves',
        'geo_sunset':           '_apply_geo_sunset',
        'geo_fire':             '_apply_geo_fire_gradient',
        'geo_galaxy':           '_apply_geo_galaxy',
        'geo_rainbow_flow':     '_apply_geo_rainbow_flow',
        'geo_neon_pulse':       '_apply_geo_neon_pulse',
        'geo_tropical':         '_apply_geo_tropical',
        'geo_silk':             '_apply_geo_silk',
        'geo_tide':             '_apply_geo_tide',
        # Additional effects
        'geo_clouds':           '_apply_geo_clouds',
        'geo_mist':             '_apply_geo_mist',
        'geo_candlelight':      '_apply_geo_candlelight',
        'geo_moonlight':        '_apply_geo_moonlight',
        'geo_ripple':           '_apply_geo_ripple',
        'geo_meditation':       '_apply_geo_meditation',
        'geo_dreamscape':       '_apply_geo_dreamscape',
        'geo_northern_lights':  '_apply_geo_northern_lights',
        'geo_waterfall':        '_apply_geo_waterfall',
        'geo_ember':            '_apply_geo_ember',
        'geo_prism_effect':     '_apply_geo_prism',
        'geo_coral':            '_apply_geo_coral',
        'geo_bioluminescence':  '_apply_geo_bioluminescence',
        'geo_zen':              '_apply_geo_zen',
        'geo_random_fade':      '_apply_geo_random_fade',
        'geo_breathing_wave':   '_apply_geo_breathing_wave',
        'geo_twinkle_fade':     '_apply_geo_twinkle_fade',
        'geo_spotlight_wander': '_apply_geo_spotlight_wander',
        'geo_cascade_dim':      '_apply_geo_cascade_dim',
        'geo_firefly':          '_apply_geo_firefly',
        'geo_rolling_blackout': '_apply_geo_rolling_blackout',
        'geo_rain_fade':        '_apply_geo_rain_fade',
        'geo_nebula':           '_apply_geo_nebula',
        'geo_lanterns':         '_apply_geo_lanterns',
        'geo_jellyfish':        '_apply_geo_jellyfish',
        'geo_morning_mist':     '_apply_geo_morning_mist',
        'geo_stardust':         '_apply_geo_stardust',
        'pixel_orbits':         '_apply_pixel_orbits',
        'pixel_starfield':      '_apply_pixel_starfield',
        'pixel_diamond':        '_apply_pixel_diamond',
        'pixel_butterfly':      '_apply_pixel_butterfly',
        'pixel_spinner':        '_apply_pixel_spinner',
        'pixel_ripple_pool':    '_apply_pixel_ripple_pool',
        # Aliases for old / alternative dispatch keys
        'geo_fire_gradient':    '_apply_geo_fire_gradient',
        'geo_prism':            '_apply_geo_prism',
        # Dim-overlay variants
        'geo_heartbeat_dim':    '_apply_geo_heartbeat_dim',
        'geo_aurora_dim':       '_apply_geo_aurora_dim',
    }

    # Ensemble effect ids whose handler method name differs from the
    # f"_apply_{effect_type}" convention.  Used by the HTP buffer dispatch so
    # stored presets carrying the un-aliased id still animate.
    _ENSEMBLE_METHOD_ALIASES = {
        'ensemble_meditation': '_apply_ensemble_meditation_room',
    }

    def __init__(self, artnet, project, on_effect_state_change: Optional[Callable] = None):
        """
        Args:
            artnet: ArtNetOutput instance for sending DMX
            project: LightingProject with fixtures and groups
            on_effect_state_change: Callback function called when effects start/stop
        """
        self.artnet = artnet
        self.project = project
        self._running = False
        self._execute_mode = False  # True when started from Execute section (overrides overlay)
        self._stop_event = Event()
        self._thread: Optional[Thread] = None
        self._current_effect: Optional[EffectParameters] = None
        self._effect_start_time = 0.0
        self._on_effect_state_change = on_effect_state_change  # Callback for effect start/stop
        self._global_speed_multiplier = 1.0  # Global speed control (0.25x to 4x)
        self._fader_level = 1.0  # Fader scaling level (0.0 to 1.0)
        
        # Group intensity support - per-group intensity scaling (0.0 to 1.0)
        self._group_intensities: dict[str, float] = {}  # group_id -> intensity (0.0-1.0)
        self._fixture_group_cache: dict[str, list[str]] = {}  # fixture_id -> list of group_ids (cache)

        # (universe, channel) -> fixture lookup used by the HTP merge loop to
        # apply per-fixture group masters / fixture-type caps to the final
        # merged values.  Invalidated by clear_group_intensities() and rebuilt
        # lazily on next merge.
        self._channel_fixture_cache: dict[tuple[int, int], object] = {}

        # Fixture type brightness caps - per-profile maximum intensity (0.0 to 1.0)
        # This is a HARD CAP - fixtures can never exceed this brightness
        self._fixture_type_caps: dict[str, float] = {}  # profile_name -> max_intensity (0.0-1.0)
        
        # Pause support
        self._paused = False  # When True, effect loops freeze in place
        
        # Multi-effect HTP blending support
        self._active_effects: dict[str, ActiveEffect] = {}  # preset_id -> ActiveEffect
        self._htp_enabled = True  # Enable HTP blending for multiple concurrent effects
        self._merge_thread: Optional[Thread] = None
        self._merge_stop_event = Event()
        
        # Override fader support - fixtures controlled by override faders are excluded
        # from effect engine output. Last-moved fader wins for shared fixtures.
        self._override_fixtures: dict[str, str] = {}  # fixture_id -> fader_id (which fader owns it)
        self._override_fader_order: list[str] = []  # fader_ids ordered by last-moved (most recent last)
        self._override_effect_states: dict[str, dict] = {}  # fader_id -> {effect, fader_level, stop_event, thread}
        self._thread_fader_level = _ThreadLocal()  # Thread-local fader level for override loops
        self._movement_override_movers: set = set()  # fixture_ids under movement-only override
        
        # Visualizer overlay exclusion — channels controlled by the viz overlay
        # are added here so the HTP merge and effect loops skip them, preventing
        # the effect engine and overlay from fighting each other.
        self._viz_overlay_channels: set = set()  # {(universe, channel_addr), ...}
        
        # Fixture control dialog exclusion — channels driven by the
        # live FixtureControlDialog are parked here so effects skip them.
        self._fixture_control_channels: set = set()  # {(universe, channel_addr), ...}
        
        # Continuous override DMX re-assertion — group/programme faders store
        # their desired DMX values here.  The merge loop writes them on every
        # frame (40 fps) so that even if a code path is missed, override values
        # are never lost.  Keyed by fader_id for clean per-fader cleanup.
        self._override_dmx_values: dict[str, dict[tuple[int, int], int]] = {}  # fader_id -> {(uni, ch): value}
        
        # Spatial DMX mapper exclusion — reference to the SpatialDMXMapper's
        # controlled_channels set.  Populated when the spatial mapper is
        # enabled, checked on the same hot paths as the overlay set.
        self._viz_spatial_channels: set = set()  # {(universe, channel_addr), ...}
        
        # Pre-bind the overlay check for hot-path usage (avoids repeated attr lookups)
        self._is_overlay_channel = self._check_overlay_channel
        
        # Movement ramp-in state — per-fixture starting pan/tilt captured just before
        # a new movement pattern begins, so we can smoothly interpolate from "where the
        # fixture is" to "where the movement wants it".
        self._movement_start_positions: dict[str, tuple[int, int]] = {}  # fixture_id -> (pan_coarse, tilt_coarse)
        self._movement_ramp_start_time: float = 0.0  # time.time() when the ramp started
    
    # ------------------------------------------------------------------
    # Movement ramp-in helpers
    # ------------------------------------------------------------------

    def _capture_current_pan_tilt(self, fixtures: list) -> dict[str, tuple[int, int]]:
        """Read current pan/tilt DMX values for each mover fixture from the Art-Net
        buffer and return them as {fixture_id: (pan_coarse, tilt_coarse)}.
        
        Non-mover fixtures are silently skipped.
        """
        positions: dict[str, tuple[int, int]] = {}
        for fixture in fixtures:
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            pan = None
            tilt = None
            for i, ch in enumerate(mode.channels):
                ch_type = ch.type.lower()
                addr = fixture.address + i
                if ch_type == 'pan':
                    pan = self.artnet.get_channel(fixture.universe, addr) or 0
                elif ch_type == 'tilt':
                    tilt = self.artnet.get_channel(fixture.universe, addr) or 0
            if pan is not None and tilt is not None:
                positions[fixture.id] = (pan, tilt)
        return positions

    def _get_ramp_in_blend(self, start_time: float) -> float:
        """Return a 0.0→1.0 blend factor for the movement ramp-in.
        
        0.0 = effect just started, use 100 % starting position.
        1.0 = ramp-in complete, use 100 % target (movement pattern) position.
        Uses a smooth ease-in-out curve for natural-looking motion.
        """
        elapsed = time.time() - start_time
        if elapsed >= MOVEMENT_RAMP_IN_SECONDS:
            return 1.0
        t = elapsed / MOVEMENT_RAMP_IN_SECONDS
        # Smooth-step curve (ease-in / ease-out)
        return t * t * (3.0 - 2.0 * t)

    def _blend_pan_tilt(self, fixture_id: str, target_pan: int, target_tilt: int,
                        start_positions: dict, blend: float) -> tuple[int, int]:
        """Blend between a fixture's captured start position and the target position.
        
        Args:
            fixture_id: The fixture ID to look up start positions for.
            target_pan: The movement-pattern target pan (coarse, 0-255).
            target_tilt: The movement-pattern target tilt (coarse, 0-255).
            start_positions: Dict from _capture_current_pan_tilt.
            blend: 0.0 → use start position, 1.0 → use target position.
        
        Returns:
            (blended_pan, blended_tilt) as integers 0-255.
        """
        if blend >= 1.0 or fixture_id not in start_positions:
            return (target_pan, target_tilt)
        start_pan, start_tilt = start_positions[fixture_id]
        pan = int(start_pan + (target_pan - start_pan) * blend)
        tilt = int(start_tilt + (target_tilt - start_tilt) * blend)
        return (max(0, min(255, pan)), max(0, min(255, tilt)))

    def _blend_pan_tilt_16bit(self, fixture_id: str, target_pan16: int, target_tilt16: int,
                              start_positions: dict, blend: float) -> tuple[int, int]:
        """Like _blend_pan_tilt but works in 16-bit (0-65535) domain.
        
        start_positions stores 8-bit coarse values, so we convert them to 16-bit
        (coarse << 8) for interpolation.
        """
        if blend >= 1.0 or fixture_id not in start_positions:
            return (target_pan16, target_tilt16)
        start_pan, start_tilt = start_positions[fixture_id]
        start_pan16 = start_pan << 8
        start_tilt16 = start_tilt << 8
        pan16 = int(start_pan16 + (target_pan16 - start_pan16) * blend)
        tilt16 = int(start_tilt16 + (target_tilt16 - start_tilt16) * blend)
        return (max(0, min(65535, pan16)), max(0, min(65535, tilt16)))

    
    def _safe_start_thread(self, target, args, name: str = "effect") -> bool:
        """Safely create and start a thread with error handling.
        
        Args:
            target: Thread target function
            args: Arguments for the target
            name: Name for logging purposes
            
        Returns:
            True if thread started successfully, False otherwise
        """
        try:
            self._thread = Thread(target=target, args=args, daemon=True)
            self._thread.start()
            print(f"[Effect] Started {name} thread")
            return True
        except TypeError as e:
            # Workaround for potential Python 3.14 threading bug
            print(f"[Effect] Thread creation failed for {name}: {e}")
            return False
    
    def set_update_callback(self, callback: Callable):
        """Set callback for effect state updates."""
        self._on_update = callback
    
    def pause(self):
        """Pause all effect animations - effects freeze in current state."""
        self._paused = True
        print("[Effect] Effects paused")
    
    def resume(self):
        """Resume effect animations from where they were paused."""
        self._paused = False
        print("[Effect] Effects resumed")
    
    @property
    def is_paused(self) -> bool:
        """Check if effects are paused."""
        return self._paused
    
    @property
    def global_speed_multiplier(self) -> float:
        """Get the global speed multiplier (0.1x to 4x)."""
        return self._global_speed_multiplier
    
    @global_speed_multiplier.setter
    def global_speed_multiplier(self, value: float):
        """Set the global speed multiplier (clamped to 0.1x - 4x)."""
        self._global_speed_multiplier = max(0.1, min(4.0, value))
        # Note: Removed print statement to prevent jitter during rapid fader movement
    
    def set_group_intensity(self, group_id: str, intensity: float):
        """Set intensity for a group (0.0 to 1.0), or None to release control.
        
        All fixtures in this group will have their output scaled by this intensity.
        If a fixture is in multiple groups, the highest group intensity applies.
        
        Args:
            group_id: The group's unique ID
            intensity: Intensity value (0.0 = off, 1.0 = full, None = release control)
        """
        if intensity is None:
            # Release control - remove from dict so effect engine takes over
            if group_id in self._group_intensities:
                del self._group_intensities[group_id]
            return
        clamped = max(0.0, min(1.0, intensity))
        self._group_intensities[group_id] = clamped
    
    def get_group_intensity(self, group_id: str) -> float:
        """Get intensity for a group (default 1.0 if not set)."""
        return self._group_intensities.get(group_id, 1.0)
    
    def set_fixture_type_cap(self, profile_name: str, max_intensity: float):
        """Set maximum brightness cap for a fixture type (0.0 to 1.0).
        
        This is a HARD CAP - fixtures of this type can NEVER exceed this brightness,
        regardless of effect intensity, group faders, or master level.
        
        Args:
            profile_name: The fixture profile name (e.g., 'Spot', 'Wash', 'Strobe')
            max_intensity: Maximum intensity (0.0 = off, 1.0 = full)
        """
        clamped = max(0.0, min(1.0, max_intensity))
        old_val = self._fixture_type_caps.get(profile_name, None)
        if old_val != clamped:
            self._fixture_type_caps[profile_name] = clamped
    
    def get_fixture_type_cap(self, profile_name: str) -> float:
        """Get maximum brightness cap for a fixture type (default 1.0 if not set)."""
        return self._fixture_type_caps.get(profile_name, 1.0)
    
    def clear_fixture_type_caps(self):
        """Reset all fixture type caps to 1.0 (full)."""
        self._fixture_type_caps.clear()
    
    def _get_fixture_type_cap(self, fixture) -> float:
        """Get the brightness cap for a fixture based on its profile.
        
        Args:
            fixture: The fixture object
            
        Returns:
            Maximum intensity (0.0 to 1.0)
        """
        if not self._fixture_type_caps:
            return 1.0  # No caps set, full output
        
        profile_name = fixture.profile.name
        return self._fixture_type_caps.get(profile_name, 1.0)
    
    def clear_group_intensities(self):
        """Reset all group intensities to 1.0 (full)."""
        self._group_intensities.clear()
        self._fixture_group_cache.clear()
        self._channel_fixture_cache.clear()
    
    def _is_fixture_under_group_fader(self, fixture) -> bool:
        """Check if a fixture is under active group fader control.
        
        Returns True if any group this fixture belongs to has a non-zero
        intensity set via set_group_intensity (i.e. a group fader is up).
        """
        if not self._group_intensities:
            return False
        
        fixture_id = fixture.id
        if fixture_id not in self._fixture_group_cache:
            groups = []
            for group in self.project.groups:
                if fixture_id in group.fixture_ids:
                    groups.append(group.id)
            self._fixture_group_cache[fixture_id] = groups
        
        for gid in self._fixture_group_cache[fixture_id]:
            if self._group_intensities.get(gid, 0) > 0:
                return True
        return False

    # --- Override Fader Support ---
    
    def set_override_fixtures(self, fader_id: str, fixture_ids: list[str]):
        """Register fixtures as overridden by a specific fader.
        
        Overridden fixtures are excluded from effect engine output.
        Last-moved fader wins if multiple override faders share fixtures.
        
        Args:
            fader_id: Unique fader identifier (e.g., "group_<uuid>")
            fixture_ids: List of fixture IDs this fader controls
        """
        # Update fader ordering (most recently moved = last in list)
        if fader_id in self._override_fader_order:
            self._override_fader_order.remove(fader_id)
        self._override_fader_order.append(fader_id)
        
        # Re-assign fixtures: last-moved fader wins for any shared fixtures
        for fid in fixture_ids:
            self._override_fixtures[fid] = fader_id
        
        # For earlier faders that lost fixtures, update their claims
        # (earlier faders keep fixtures not claimed by later faders)
    
    def release_override_fixtures(self, fader_id: str):
        """Release all fixtures owned by a fader back to the effect engine.
        
        Called when an override fader goes to zero.
        
        Args:
            fader_id: The fader releasing control
        """
        # Remove all fixtures owned by this fader
        to_remove = [fid for fid, owner in self._override_fixtures.items() if owner == fader_id]
        for fid in to_remove:
            del self._override_fixtures[fid]
        
        # Remove from ordering
        if fader_id in self._override_fader_order:
            self._override_fader_order.remove(fader_id)
        
        # Clear stored DMX values for this fader
        self._override_dmx_values.pop(fader_id, None)
        
        # If no active effects and no remaining overrides, stop the merge
        # loop so the background thread doesn't spin idle.
        if not self._active_effects and not self._override_dmx_values:
            self._stop_merge_loop()
    
    # ------------------------------------------------------------------
    # Override DMX value storage (continuous re-assertion)
    # ------------------------------------------------------------------
    
    def store_override_dmx(self, fader_id: str, values: dict):
        """Store per-channel DMX values for continuous re-assertion.
        
        Called by the GUI whenever a group/programme fader writes DMX.
        The merge loop will write these values on every frame (40 fps)
        so that override values are bulletproof against missed code paths.
        
        Args:
            fader_id: The fader storing these values (e.g. "group_<uuid>")
            values: dict of {(universe, channel): dmx_value}
        """
        self._override_dmx_values[fader_id] = values
        # Ensure the merge loop is running so _reassert_override_dmx fires
        # even when no HTP effects are active.
        self._ensure_merge_loop_running()
    
    def clear_override_dmx(self, fader_id: str):
        """Clear stored DMX values for a fader (called when fader goes to 0)."""
        self._override_dmx_values.pop(fader_id, None)
    
    def _reassert_override_dmx(self):
        """Write stored override DMX values to Art-Net.
        
        Called from the merge loop so override values are continuously
        re-asserted at 40 fps, preventing any effect code path from
        overwriting group-fader commanded values.
        """
        fc = self._fixture_control_channels
        for fader_values in self._override_dmx_values.values():
            for (uni, ch), value in fader_values.items():
                if fc and (uni, ch) in fc:
                    continue  # Fixture control dialog owns this channel
                universe = self.artnet.get_universe(uni)
                if universe:
                    universe.set_channel(ch, value)
    
    def is_fixture_overridden(self, fixture_id: str) -> bool:
        """Check if a fixture is currently controlled by an override fader."""
        return fixture_id in self._override_fixtures
    
    def get_non_overridden_fixtures(self, fixtures: list) -> list:
        """Filter a fixture list to only include fixtures NOT under override control.
        
        Args:
            fixtures: List of fixture objects
            
        Returns:
            List of fixtures not currently overridden
        """
        if not self._override_fixtures:
            return fixtures  # Fast path: no overrides active
        return [f for f in fixtures if f.id not in self._override_fixtures]
    
    def clear_all_overrides(self):
        """Release all override claims (e.g., on project close)."""
        # Stop any running override effect loops first
        for fader_id in list(self._override_effect_states.keys()):
            self.stop_override_effect(fader_id)
        self._override_fixtures.clear()
        self._override_fader_order.clear()
        self._override_dmx_values.clear()
        self._movement_override_movers.clear()
        if hasattr(self, '_movement_override_fader_movers'):
            self._movement_override_fader_movers.clear()
    
    # ── Override Fader Effect Playback ──────────────────────────────────
    # Override faders run the FULL _run_effect_loop dispatch (same as
    # normal effects) but on a separate thread with an independent stop
    # event and fader level.  This lets strobe_flash, chase, etc. work
    # identically while the override's target fixtures are excluded from
    # the main effect loop.
    
    def start_override_effect(self, fader_id: str, effect: EffectParameters, fader_level: float = 1.0):
        """Start an override effect that runs the full effect dispatch loop.
        
        Uses the same _apply_* methods as the normal effect loop but on its
        own thread and stop-event so it doesn't interfere with the main effect.
        """
        # Stop existing override effect for this fader if any
        self.stop_override_effect(fader_id)
        
        stop_event = Event()
        state = {
            'effect': effect,
            'fader_level': fader_level,
            'stop_event': stop_event,
            'thread': None,
        }
        self._override_effect_states[fader_id] = state
        
        # Get target fixtures
        sort_by_position = (effect.effect_type in ('chase', 'rainbow')
                            or effect.effect_type.startswith('geo_')
                            or effect.effect_type.startswith('pixel_'))
        fixtures = self.get_target_fixtures(effect, sort_by_position=sort_by_position)
        
        if not fixtures:
            print(f"[Override Effect] No fixtures for override fader {fader_id}")
            return
        
        # Register these fixtures as overridden so the main effect loop and
        # HTP merge skip them — prevents the two threads from fighting over
        # the same DMX channels (which causes visible flashing).
        #
        # However, for MOVEMENT-ONLY effects (effect_type doesn't match any
        # color/intensity dispatch), we must NOT override all fixtures.
        # Movement only writes pan/tilt channels — it doesn't conflict with
        # the main effect's color/intensity output.  Marking all fixtures as
        # overridden would make the main effect appear dead because it would
        # have zero active_fixtures.
        #
        # For movement-only overrides we only override the MOVER fixtures so
        # the main effect skips movement on them (avoids pan/tilt fighting)
        # but still renders their colour/intensity.
        _COLOR_EFFECT_TYPES = {
            'strobe', 'pulse', 'chase', 'fade', 'rainbow', 'static',
            'pixel_chase', 'pixel_rainbow', 'pixel_wipe',
            'strobe_flash', 'strobe_hscan', 'strobe_vscan',
            'strobe_chase', 'strobe_expand', 'strobe_random',
            'strobe_alternating', 'strobe_build',
        }
        has_color_dispatch = (
            effect.effect_type in _COLOR_EFFECT_TYPES
            or effect.effect_type.startswith('ensemble_')
            or effect.effect_type.startswith('geo_')
            or effect.effect_type.startswith('pixel_')
        )
        has_movement_only = (
            not has_color_dispatch
            and effect.movement_pattern
            and effect.movement_pattern.lower() not in ('none', '')
        )
        
        if has_movement_only:
            # Movement-only override (e.g. effect_type='movement'):
            # Only claim MOVER fixtures as overridden — non-movers stay with
            # the main effect so it doesn't lose its pixel/wash fixtures.
            # The override loop will apply static color + movement to movers.
            mover_fixtures = [f for f in fixtures if self._fixture_has_pan_tilt(f)]
            mover_ids = [f.id for f in mover_fixtures]
            if mover_ids:
                self.set_override_fixtures(fader_id, mover_ids)
            # Also track for movement-skip in main loop
            self._movement_override_movers.update(mover_ids)
            if not hasattr(self, '_movement_override_fader_movers'):
                self._movement_override_fader_movers = {}
            self._movement_override_fader_movers[fader_id] = set(mover_ids)
            # Restrict fixtures list to movers only for the override loop thread
            fixtures = mover_fixtures
            print(f"[Override Effect] Movement-only override — claiming {len(mover_ids)} MOVER fixtures (non-movers stay with main effect)")
        else:
            # Color/intensity override: register all target fixtures
            fixture_ids = [f.id for f in fixtures]
            self.set_override_fixtures(fader_id, fixture_ids)
        
        # Log detailed info about what the override is claiming
        total_project = len(self.project.fixtures) if self.project else 0
        main_running = self._running
        main_effect_type = self._current_effect.effect_type if self._current_effect else 'NONE'
        overridden_count = len(self._override_fixtures)
        print(f"[Override Effect] Starting {effect.effect_type} on {len(fixtures)}/{total_project} fixtures for {fader_id}")
        print(f"[Override Effect]   target_groups={effect.target_groups}, target_fixtures={effect.target_fixtures}")
        print(f"[Override Effect]   has_color_dispatch={has_color_dispatch}, movement_only={has_movement_only}")
        print(f"[Override Effect]   Main effect running={main_running}, type={main_effect_type}")
        print(f"[Override Effect]   Override fixtures claimed: {overridden_count}")
        
        thread = Thread(
            target=self._run_override_effect_loop,
            args=(fader_id, state, fixtures),
            daemon=True
        )
        state['thread'] = thread
        thread.start()
    
    def stop_override_effect(self, fader_id: str):
        """Stop an override effect."""
        state = self._override_effect_states.pop(fader_id, None)
        if state:
            state['stop_event'].set()
            thread = state.get('thread')
            if thread and thread.is_alive():
                thread.join(timeout=0.5)
            print(f"[Override Effect] Stopped effect for {fader_id}")
        # Release the override claim so other loops can control
        # these fixtures again.
        self.release_override_fixtures(fader_id)
        # Also release movement-only override movers owned by this fader
        owned_movers = getattr(self, '_movement_override_fader_movers', {}).pop(fader_id, set())
        if owned_movers:
            self._movement_override_movers -= owned_movers
            print(f"[Override Effect] Released {len(owned_movers)} movement-only movers for {fader_id}")
    
    def set_override_fader_level(self, fader_id: str, level: float):
        """Update fader level for a running override effect."""
        state = self._override_effect_states.get(fader_id)
        if state:
            state['fader_level'] = max(0.0, min(1.0, level))
    
    def _run_override_effect_loop(self, fader_id: str, state: dict, fixtures: list):
        """Effect loop for an override fader — runs full dispatch like _run_effect_loop.
        
        Temporarily sets self._fader_level per-frame so all _apply_* methods
        use this override's fader level rather than the main effect's.
        """
        frame_time = 1.0 / 50  # 50fps — must exceed Art-Net send rate (44fps)
        stop_event: Event = state['stop_event']
        effect: EffectParameters = state['effect']
        
        accumulated_phase = 0.0
        last_frame_time = time.time()
        original_bpm = max(1, effect.speed_bpm) if effect.speed_bpm else 120
        original_cycle_seconds = effect.cycle_seconds if effect.cycle_seconds and effect.cycle_seconds > 0 else 0
        
        # Cache movers
        all_movers = [f for f in fixtures if self._fixture_has_pan_tilt(f)]
        all_static = [f for f in fixtures if not self._fixture_has_pan_tilt(f)]
        
        # Capture current pan/tilt for smooth ramp-in when movement starts
        override_start_positions = self._capture_current_pan_tilt(all_movers)
        override_ramp_start = time.time()
        
        # Strobe tracking
        strobe_color_applied_to_movers = False
        
        print(f"[Override Effect] Loop started for {fader_id}: {effect.effect_type}")
        
        while not stop_event.is_set():
            loop_start = time.perf_counter()
            
            if self._paused:
                time.sleep(frame_time)
                last_frame_time = time.time()
                continue
            
            # Calculate timing
            current_time = time.time()
            delta_time = current_time - last_frame_time
            last_frame_time = current_time
            
            current_bpm = max(1, effect.speed_bpm)
            if original_cycle_seconds > 0:
                cycle_duration = original_cycle_seconds / ((current_bpm / original_bpm) * self._global_speed_multiplier)
            elif effect.effect_type == 'movement':
                # Movement effects use a much slower time base (same as main loop)
                effective_bpm = max(2, effect.speed_bpm / 10)
                cycle_duration = 60.0 / (effective_bpm * self._global_speed_multiplier)
            elif effect.effect_type == 'chase':
                cycle_duration = 60.0 / (max(2, effect.speed_bpm / 4) * self._global_speed_multiplier)
            else:
                cycle_duration = 60.0 / (current_bpm * self._global_speed_multiplier)
            
            phase_increment = delta_time / cycle_duration
            accumulated_phase = (accumulated_phase + phase_increment) % 1.0
            phase = accumulated_phase
            
            has_movement = effect.movement_pattern and effect.movement_pattern.lower() not in ('none', '')
            movers = all_movers
            non_movers = all_static
            
            # Set thread-local fader level so _apply_* methods use this override's level
            # (thread-local avoids race conditions with the main effect loop)
            self._thread_fader_level.value = state['fader_level']
            
            try:
                # ── Dispatch based on effect type (same as _run_effect_loop) ──
                if effect.effect_type == 'strobe':
                    if movers and non_movers:
                        self._apply_strobe(non_movers, effect, phase)
                        if not strobe_color_applied_to_movers:
                            self._apply_strobe(movers, effect, phase)
                            strobe_color_applied_to_movers = True
                        self._apply_strobe_intensity_only(movers, effect, phase)
                    else:
                        self._apply_strobe(fixtures, effect, phase)
                elif effect.effect_type == 'pulse':
                    self._apply_pulse(fixtures, effect, phase)
                elif effect.effect_type == 'chase':
                    self._apply_chase(fixtures, effect, phase)
                elif effect.effect_type == 'fade':
                    self._apply_fade(fixtures, effect, phase)
                elif effect.effect_type == 'rainbow':
                    self._apply_rainbow(fixtures, effect, phase)
                elif effect.effect_type == 'pixel_chase':
                    self._apply_pixel_chase(fixtures, effect, phase)
                elif effect.effect_type == 'pixel_rainbow':
                    self._apply_pixel_rainbow(fixtures, effect, phase)
                elif effect.effect_type == 'pixel_wipe':
                    self._apply_pixel_wipe(fixtures, effect, phase)
                elif effect.effect_type == 'static':
                    color_palette = effect.color_palette if effect.color_palette else []
                    if color_palette:
                        self._apply_static_with_palette(fixtures, effect, skip_pan_tilt=has_movement)
                    else:
                        self.apply_static(fixtures, effect.color, effect.intensity,
                                        color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                        effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                        skip_pan_tilt=has_movement,
                                        **self._gobo_kwargs(effect))
                elif effect.effect_type == 'strobe_flash':
                    self._apply_strobe_flash(fixtures, effect, phase)
                elif effect.effect_type == 'strobe_hscan':
                    self._apply_strobe_hscan(fixtures, effect, phase)
                elif effect.effect_type == 'strobe_vscan':
                    self._apply_strobe_vscan(fixtures, effect, phase)
                elif effect.effect_type == 'strobe_chase':
                    self._apply_strobe_chase(fixtures, effect, phase)
                elif effect.effect_type == 'strobe_expand':
                    self._apply_strobe_expand(fixtures, effect, phase)
                elif effect.effect_type == 'strobe_random':
                    self._apply_strobe_random(fixtures, effect, phase)
                elif effect.effect_type == 'strobe_alternating':
                    self._apply_strobe_alternating(fixtures, effect, phase)
                elif effect.effect_type == 'strobe_build':
                    self._apply_strobe_build(fixtures, effect, phase)
                elif effect.effect_type.startswith('ensemble_'):
                    # Route ensemble effects
                    method_name = f"_apply_{effect.effect_type}"
                    method = getattr(self, method_name, None)
                    if method:
                        method(fixtures, effect, phase)
                elif effect.effect_type == 'movement':
                    # Movement-type effect: apply static color to claimed fixtures
                    # so they get proper color/intensity from the override fader.
                    # Movement overlay is applied below.
                    self.apply_static(fixtures, effect.color, effect.intensity,
                                    color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                    effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                    skip_pan_tilt=has_movement,
                                    **self._gobo_kwargs(effect))
                
                # Apply movement overlay if needed
                if has_movement and movers:
                    override_ramp = self._get_ramp_in_blend(override_ramp_start)
                    self._apply_movement(movers, effect, phase,
                                         start_positions=override_start_positions,
                                         ramp_blend=override_ramp)
                    
            except Exception as e:
                print(f"[Override Effect] Error in {fader_id}: {e}")
            
            # Frame rate control
            elapsed = time.perf_counter() - loop_start
            sleep_time = frame_time - elapsed
            if sleep_time > 0:
                time.sleep(sleep_time)
        
        print(f"[Override Effect] Loop ended for {fader_id}")
    
    def _check_overlay_channel(self, universe: int, addr: int) -> bool:
        """Fast check if a channel is owned by the visualizer overlay,
        the spatial DMX mapper, or the fixture control dialog.
        
        Returns True if the channel should be SKIPPED by the effect engine
        because an external source is controlling it.
        """
        key = (universe, addr)
        oc = self._viz_overlay_channels
        if oc and key in oc:
            return True
        sc = self._viz_spatial_channels
        if sc and key in sc:
            return True
        fc = self._fixture_control_channels
        if fc and key in fc:
            return True
        return False
    
    def has_active_output(self) -> bool:
        """Return True if a *preset*, *execute effect*, or *override fader*
        is actively generating DMX output that drives colour/intensity
        channels.  Used by the video overlay to yield control.

        Movement/position-only layers are excluded: they only control
        pan/tilt and should not cause the overlay to stop driving colour.

        The Create-tab main effect (``_running`` without ``_execute_mode``)
        is intentionally excluded: the Create tab only tweaks movement
        (pan/tilt) while the overlay continues to drive colour channels.
        Overlay channel checks in the effect-engine hot paths prevent the
        two from clashing."""
        _MOVEMENT_ONLY_TYPES = {'movement', 'position'}
        if self._active_effects:
            for ae in list(self._active_effects.values()):
                lt = getattr(ae.effect, 'layer_type', '') or ''
                if lt not in _MOVEMENT_ONLY_TYPES:
                    return True
        if bool(self._override_fixtures):
            return True
        if self._running and self._execute_mode:
            return True
        return False
    
    def _get_fixture_group_intensity(self, fixture) -> float:
        """Get the effective intensity for a fixture based on its group memberships.
        
        If a fixture is in multiple groups, returns the HIGHEST group intensity (HTP).
        If a fixture is not in any group or no group intensities are set, returns 1.0.
        
        Args:
            fixture: The fixture object
            
        Returns:
            Effective intensity (0.0 to 1.0)
        """
        if not self._group_intensities:
            return 1.0  # No group intensities set, full output
        
        # Check cache first
        fixture_id = fixture.id
        if fixture_id not in self._fixture_group_cache:
            # Build cache for this fixture - find all groups it belongs to
            groups = []
            for group in self.project.groups:
                if fixture_id in group.fixture_ids:
                    groups.append(group.id)
            self._fixture_group_cache[fixture_id] = groups
        
        group_ids = self._fixture_group_cache[fixture_id]
        
        if not group_ids:
            return 1.0  # Fixture not in any group - full output
        
        # Get highest intensity from all groups this fixture belongs to (HTP)
        max_intensity = 0.0
        has_any_group_intensity = False
        for gid in group_ids:
            if gid in self._group_intensities:
                has_any_group_intensity = True
                max_intensity = max(max_intensity, self._group_intensities[gid])
        
        # If no group intensities are set for any of this fixture's groups, return 1.0
        # This allows fixtures to work normally until group faders are used
        if not has_any_group_intensity:
            return 1.0
        
        return max_intensity
    
    def _is_preview_active(self) -> bool:
        """Check if position preview is active.
        
        When position preview is active, NO code should modify pan/tilt values.
        This ensures the user's preview position takes absolute priority.
        """
        if hasattr(self, 'is_position_preview_active') and callable(self.is_position_preview_active):
            result = self.is_position_preview_active()
            # Debug log only when preview IS active (to avoid spam)
            if result:
                # Only log occasionally to avoid spam
                if not hasattr(self, '_preview_log_counter'):
                    self._preview_log_counter = 0
                self._preview_log_counter += 1
                if self._preview_log_counter % 200 == 1:  # Log every ~5 seconds at 40fps
                    print(f"[EffectEngine] Position preview ACTIVE - pan/tilt writes blocked")
            return result
        return False
    
    def get_target_fixtures(self, effect: EffectParameters, sort_by_position: bool = False) -> list:
        """Get list of fixtures targeted by effect.
        
        Args:
            effect: The effect parameters containing target_groups and target_fixtures
            sort_by_position: If True, sort fixtures by physical location (location_x/location_y)
                             Direction 'forward' = left-to-right (by location_x ascending)
                             Direction 'reverse' = right-to-left (by location_x descending)
                             Direction 'top_down' = top-to-bottom (by location_y ascending)
                             Direction 'bottom_up' = bottom-to-top (by location_y descending)
        """
        fixtures = []
        
        # By specific fixture IDs
        if effect.target_fixtures:
            for fid in effect.target_fixtures:
                f = self.project.get_fixture_by_id(fid)
                if f:
                    fixtures.append(f)
        
        # By group names
        if effect.target_groups:
            if "all" in [g.lower() for g in effect.target_groups]:
                fixtures = list(self.project.fixtures)
                print(f"[get_target_fixtures] target_groups includes 'all' -> selected ALL {len(fixtures)} fixtures")
                for f in fixtures[:3]:
                    print(f"  - {getattr(f, 'label', 'unnamed')} ({f.profile.name if f.profile else 'NO_PROFILE'})")
                if len(fixtures) > 3:
                    print(f"  ... and {len(fixtures)-3} more")
            else:
                for group_name in effect.target_groups:
                    group = self._find_group_fuzzy(group_name)
                    if group:
                        print(f"[Effect] Matched group '{group_name}' -> '{group.name}'")
                        for fid in group.fixture_ids:
                            f = self.project.get_fixture_by_id(fid)
                            if f and f not in fixtures:
                                fixtures.append(f)
                    else:
                        print(f"[Effect] WARNING: No group found matching '{group_name}'")
                        # Try to match by fixture type/category as fallback
                        category_fixtures = self._find_fixtures_by_category(group_name)
                        for f in category_fixtures:
                            if f not in fixtures:
                                fixtures.append(f)
        
        # Default to all if nothing specified — BUT only when not using layer_type
        # channel filtering (layer stack layers with empty groups should produce
        # no output so they don't interfere until the user picks a group).
        if not fixtures:
            layer_type = getattr(effect, 'layer_type', '') or ''
            if layer_type:
                # Layer stack layer with no group selected → intentionally empty
                print(f"[Effect] Layer type '{layer_type}' with no target fixtures — skipping")
                return []
            print("[Effect] No fixtures matched - defaulting to ALL fixtures")
            fixtures = list(self.project.fixtures)
        
        # Filter out fixtures excluded from effects
        before_count = len(fixtures)
        fixtures = [f for f in fixtures if not getattr(f, 'exclude_from_effects', False)]
        excluded_count = before_count - len(fixtures)
        if excluded_count > 0:
            print(f"[Effect] Excluded {excluded_count} fixture(s) marked as 'exclude from effects'")
        
        # Sort fixtures by physical location for wave/chase effects
        if sort_by_position:
            direction = getattr(effect, 'direction', 'forward')
            if direction in ('top_down', 'bottom_up'):
                # Sort by Y position (top to bottom or bottom to top)
                reverse = (direction == 'bottom_up')
                fixtures.sort(key=lambda f: getattr(f, 'location_y', 0.5), reverse=reverse)
                print(f"[Effect] Sorted {len(fixtures)} fixtures by location_y ({'bottom-up' if reverse else 'top-down'})")
            else:
                # Sort by X position (left to right or right to left)
                reverse = (direction == 'reverse')
                fixtures.sort(key=lambda f: getattr(f, 'location_x', 0.5), reverse=reverse)
                print(f"[Effect] Sorted {len(fixtures)} fixtures by location_x ({'right-left' if reverse else 'left-right'})")
        
        print(f"[Effect] Total fixtures targeted: {len(fixtures)}")
        return fixtures
    
    def _find_group_fuzzy(self, search_name: str):
        """Find a group with fuzzy matching."""
        search_lower = search_name.lower().strip()
        
        # Try exact match first
        group = self.project.get_group_by_name(search_name)
        if group:
            return group
        
        # Try partial matching
        for g in self.project.groups:
            group_lower = g.name.lower()
            # Check if search term is contained in group name or vice versa
            if search_lower in group_lower or group_lower in search_lower:
                return g
            # Check without "All " prefix
            if search_lower.replace("all ", "") in group_lower.replace("all ", ""):
                return g
            if group_lower.replace("all ", "") in search_lower.replace("all ", ""):
                return g
        
        # Try matching key words
        search_words = search_lower.replace("all ", "").split()
        for g in self.project.groups:
            group_words = g.name.lower().replace("all ", "").split()
            # If any significant word matches
            for sw in search_words:
                if len(sw) > 2:  # Skip short words
                    for gw in group_words:
                        if sw in gw or gw in sw:
                            return g
        
        return None
    
    def _find_fixtures_by_category(self, category_name: str) -> list:
        """Find fixtures by category/type when no group matches."""
        category_lower = category_name.lower().strip().replace('all ', '')
        fixtures = []
        
        # Map category terms to fixture profile type/category keywords
        category_keywords = {
            'mover': ['moving', 'mover', 'spot', 'beam', 'head'],
            'moving head': ['moving', 'mover', 'spot', 'beam', 'head'],
            'movers': ['moving', 'mover', 'spot', 'beam', 'head'],
            'spots': ['moving', 'mover', 'spot', 'beam', 'head'],
            'spot': ['moving', 'mover', 'spot', 'beam', 'head'],
            'par': ['par', 'can', 'uplight'],
            'pars': ['par', 'can', 'uplight'],
            'wash': ['wash', 'flood', 'fresnel', 'strobe'],  # Include strobe as potential wash-like
            'washes': ['wash', 'flood', 'fresnel', 'strobe'],  # Many strobes have RGB like wash
            'strobe': ['strobe', 'flash', 'blinder', 'atomic'],
            'strobes': ['strobe', 'flash', 'blinder', 'atomic'],
            'bar': ['bar', 'batten', 'strip', 'linear'],
            'bars': ['bar', 'batten', 'strip', 'linear'],
        }
        
        # Get keywords for this category
        keywords = category_keywords.get(category_lower, [])
        if not keywords:
            # Try partial match on category_keywords keys
            for key, kw_list in category_keywords.items():
                if key in category_lower or category_lower in key:
                    keywords = kw_list
                    break
        
        if keywords:
            for fixture in self.project.fixtures:
                profile_name = fixture.profile.name.lower() if fixture.profile else ''
                profile_category = fixture.profile.category.lower() if fixture.profile and fixture.profile.category else ''
                label = (fixture.label or '').lower()
                
                # Check if fixture matches any keyword in name, category, or label
                for kw in keywords:
                    if kw in profile_name or kw in profile_category or kw in label:
                        if fixture not in fixtures:
                            fixtures.append(fixture)
                            print(f"[Effect] Category match: '{fixture.label or fixture.profile.name}' (category: {profile_category}) matched '{category_name}'")
                        break
        
        if not fixtures:
            print(f"[Effect] No fixtures found matching category '{category_name}'")
        
        return fixtures
    
    def apply_random(self, fixtures: list, effect: 'EffectParameters'):
        """Apply random DMX values to all channels of fixtures.
        
        Fixtures in the same group get the same random values.
        
        Args:
            fixtures: List of fixtures to apply to
            effect: Effect parameters (used for target_groups to maintain grouping)
        """
        import random
        
        print(f"[Effect] Applying random values to {len(fixtures)} fixtures")
        
        # Build a map of group -> fixtures for this effect
        group_fixtures = {}  # group_id -> [fixtures]
        ungrouped = []
        
        for fixture in fixtures:
            # Find which group(s) this fixture belongs to
            fixture_groups = []
            for group in self.project.groups:
                if fixture.id in group.fixture_ids:
                    fixture_groups.append(group.id)
            
            if fixture_groups:
                # Add to the first matching group (fixtures can be in multiple groups)
                group_id = fixture_groups[0]
                if group_id not in group_fixtures:
                    group_fixtures[group_id] = []
                group_fixtures[group_id].append(fixture)
            else:
                ungrouped.append(fixture)
        
        # Generate random values per group
        group_random_values = {}  # group_id -> {channel_type: value}
        
        for group_id in group_fixtures:
            group_random_values[group_id] = self._generate_random_channel_values()
            print(f"[Effect] Group {group_id}: Generated random values")
        
        # Apply to grouped fixtures (same values per group)
        for group_id, gfixtures in group_fixtures.items():
            random_values = group_random_values[group_id]
            for fixture in gfixtures:
                self._apply_random_to_fixture(fixture, random_values)
        
        # Apply to ungrouped fixtures (each gets unique random values)
        for fixture in ungrouped:
            random_values = self._generate_random_channel_values()
            self._apply_random_to_fixture(fixture, random_values)
            print(f"[Effect] Ungrouped fixture {fixture.label or fixture.profile.name}: Unique random values")
    
    def _generate_random_channel_values(self) -> dict:
        """Generate random DMX values for each channel type."""
        import random
        return {
            'dimmer': random.randint(128, 255),  # Keep some brightness
            'red': random.randint(0, 255),
            'green': random.randint(0, 255),
            'blue': random.randint(0, 255),
            'white': random.randint(0, 255),
            'cool_white': random.randint(0, 255),
            'warm_white': random.randint(0, 255),
            'amber': random.randint(0, 255),
            'uv': random.randint(0, 255),
            'color_wheel': random.randint(0, 127),  # Usually lower values for solid colors
            'gobo': random.randint(0, 64),  # Lower values for common gobos
            'pan': random.randint(30, 225),  # Avoid extremes
            'tilt': random.randint(30, 225),
            'effect': random.randint(0, 127),
            'macro': random.randint(0, 127),
            'speed': random.randint(64, 192),
            'shutter': 255,  # Keep shutter open
            'strobe': 0,  # No strobe by default
            'focus': random.randint(64, 192),
            'zoom': random.randint(64, 192),
            'prism': random.randint(0, 64),
        }
    
    def _apply_random_to_fixture(self, fixture, random_values: dict):
        """Apply random values to a single fixture based on its mode channels."""
        mode = fixture.profile.get_mode(fixture.mode_name)
        if not mode:
            return
        
        uni = self.artnet.get_universe(fixture.universe)
        if not uni:
            return
        
        for i, channel in enumerate(mode.channels):
            ch_type = channel.type.lower()
            addr = fixture.address + i  # 1-indexed for Art-Net
            
            if ch_type == 'disabled':
                value = 0
            elif ch_type in random_values:
                value = random_values[ch_type]
            elif ch_type in ('pan_fine', 'tilt_fine'):
                value = 0  # Fine channels stay at 0
            else:
                value = random_values.get('dimmer', 128)  # Default fallback
            
            uni.set_channel(addr, value)
    
    @staticmethod
    def _gobo_kwargs(effect) -> dict:
        """Extract gobo/gobo2/rotation kwargs from an effect for apply_static()."""
        return {
            'gobo': getattr(effect, 'gobo_value', 0) or None,
            'gobo2': getattr(effect, 'gobo2_value', 0) or None,
            'gobo_rotation': getattr(effect, 'gobo_rotation_value', 0) or None,
            'gobo2_rotation': getattr(effect, 'gobo2_rotation_value', 0) or None,
        }

    def apply_static(self, fixtures: list, color: str, intensity: int, pan: int = None, tilt: int = None, macro: int = None, color_wheel_value: int = -1, effect_channel_value: int = -1, gobo: int = None, skip_pan_tilt: bool = False, gobo2: int = None, gobo_rotation: int = None, gobo2_rotation: int = None):
        """Apply a static color/intensity to fixtures.
        
        Args:
            fixtures: List of fixtures to apply to
            color: Hex color string
            intensity: 0-100 intensity (will be combined with master_level)
            pan: Optional pan value 0-255 for moving heads
            tilt: Optional tilt value 0-255 for moving heads
            macro: Optional macro/type channel value 0-255
            color_wheel_value: IGNORED - always uses fixture's own color wheel mapping
            effect_channel_value: Optional effect channel DMX value (-1 = not set)
            gobo: Optional gobo channel DMX value (0 = open, other = gobo pattern)
            skip_pan_tilt: If True, don't set pan/tilt/pan_fine/tilt_fine channels (for position cycling)
        """
        # Check if position preview is active - if so, always skip pan/tilt
        if hasattr(self, 'is_position_preview_active') and callable(self.is_position_preview_active):
            if self.is_position_preview_active():
                skip_pan_tilt = True

        # HTP buffer-capture redirect (set by _buffer_ensemble_adapter /
        # _buffer_geo_adapter).  When active on this thread, channel writes go
        # into the effect's DMX buffer instead of straight to Art-Net so the
        # HTP merge loop can blend them.  Inactive everywhere else, so the
        # normal direct-output path is unchanged.
        _cap_tls = getattr(self, '_buffer_capture_tls', None)
        _cap_active = _cap_tls is not None and getattr(_cap_tls, 'active', False)
        _cap_buffer = _cap_tls.buffer if _cap_active else None

        r, g, b = hex_to_rgb(color)
        
        # Use effect intensity only - master level is applied at Art-Net layer
        # when packets are built, so ALL output respects the master fader
        # Apply fader level scaling to the base intensity if set
        base_intensity = intensity
        fader_val = getattr(self, '_fader_level', 1.0)
        if fader_val is not None and fader_val != 1.0:
            # Apply fader scaling with minimum threshold to ensure visibility
            scaled_intensity = intensity * fader_val
            # Ensure minimum 5% output when fader is above 0 (prevents invisible effects)
            if fader_val > 0 and scaled_intensity < 5:
                base_intensity = 5  # Minimum 5% for visibility
            else:
                base_intensity = int(scaled_intensity)
        
        for fixture in fixtures:
            # Skip fixtures under active group/programme fader override —
            # the fader handler owns these channels and re-asserts its own DMX
            # values at 40 fps.  Writing here would cause visible flicker.
            if fixture.id in self._override_fixtures:
                continue

            # Apply group intensity scaling per-fixture
            group_intensity = self._get_fixture_group_intensity(fixture)
            fixture_intensity = base_intensity * group_intensity
            
            # Apply fixture type brightness cap as a SCALING FACTOR
            # This scales the intensity proportionally (100% cap = full, 50% cap = half brightness)
            fixture_type_cap = self._get_fixture_type_cap(fixture)
            if fixture_type_cap < 1.0:
                fixture_intensity = fixture_intensity * fixture_type_cap
            
            intensity_scale = fixture_intensity / 100.0
            
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = self.artnet.get_universe(fixture.universe)
            if not uni:
                continue
            
            # Check if this fixture has a color wheel channel
            has_color_wheel = False
            color_wheel_channel = None
            for ch in mode.channels:
                if ch.type.lower() == 'color_wheel':
                    has_color_wheel = True
                    color_wheel_channel = ch
                    break
            
            # Find the best dimmer channel - prefer one named "Dimmer" or "Master" over others
            # This handles fixtures where multiple channels are typed as dimmer but only one is the master
            first_dimmer_index = -1
            has_dimmer = False
            best_dimmer_score = -1
            
            for idx, ch in enumerate(mode.channels):
                if ch.type.lower() in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    # Score based on channel name to find the most likely master dimmer
                    ch_name = ch.name.lower() if ch.name else ''
                    score = 0
                    if 'master' in ch_name:
                        score = 3  # Highest priority
                    elif ch_name in ('dimmer', 'intensity', 'brightness'):
                        score = 2  # Named exactly as dimmer
                    elif 'dim' in ch_name or 'intensity' in ch_name:
                        score = 1  # Contains dimmer-related word
                    # else score stays 0 for generic dimmer-typed channels
                    
                    if score > best_dimmer_score:
                        best_dimmer_score = score
                        first_dimmer_index = idx
                        has_dimmer = True
            
            # Apply intensity to RGB to match Timeline Editor behavior
            # Timeline Editor always scales RGB by intensity regardless of dimmer presence
            rgb_scale = intensity_scale
            
            # Use explicit color_wheel_value if provided (>=0), otherwise look up from color
            fixture_color_wheel_value = -1
            if color_wheel_value >= 0:
                # Use the explicitly provided color wheel value
                fixture_color_wheel_value = color_wheel_value
            elif has_color_wheel and color_wheel_channel and color_wheel_channel.color_wheel_colors:
                # Look up color wheel value from the color
                fixture_color_wheel_value, matched_color_name = find_closest_color_wheel_value(
                    color, color_wheel_channel.color_wheel_colors
                )
            
            dmx_output = {}  # Track what we're sending
            
            # Check if visualizer overlay or fixture control dialog owns
            # any channels for this fixture — skip those so external sources
            # keep driving without flicker.
            overlay_channels = self._viz_overlay_channels | self._fixture_control_channels
            fixture_uni = fixture.universe
            
            # Batch updates under the universe lock to avoid tearing mid-fixture
            with (getattr(uni, 'lock', None) or nullcontext()):
                # Auto-promote second gobo channel to gobo2 (mirrors _get_fixture_capabilities)
                _gobo_count = 0
                _gobo_rot_count = 0
                for i, channel in enumerate(mode.channels):
                    ch_type = channel.type.lower()
                    if ch_type == 'gobo' and hasattr(channel, 'gobo_slots') and channel.gobo_slots:
                        _gobo_count += 1
                        if _gobo_count >= 2:
                            ch_type = 'gobo2'
                    elif ch_type in ('gobo_rotation', 'gobo_shake'):
                        _gobo_rot_count += 1
                        if _gobo_rot_count >= 2:
                            ch_type = 'gobo2_rotation'
                    addr = fixture.address + i
                    
                    # Skip channels owned by the visualizer overlay
                    if overlay_channels and (fixture_uni, addr) in overlay_channels:
                        continue
                    
                    value = 0
                    
                    if ch_type == 'disabled':
                        value = 0  # Disabled channels always output 0
                    elif ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                        # Only set the FIRST dimmer channel, skip others
                        if i == first_dimmer_index:
                            value = int(255 * intensity_scale)
                        else:
                            continue  # Skip additional dimmer channels
                    elif ch_type == 'red':
                        # Set RGB to 0 if using color wheel to prevent color mixing
                        if has_color_wheel and fixture_color_wheel_value >= 0:
                            value = 0  # Clear RGB when using color wheel
                        else:
                            value = int(r * rgb_scale)
                    elif ch_type == 'green':
                        # Set RGB to 0 if using color wheel to prevent color mixing
                        if has_color_wheel and fixture_color_wheel_value >= 0:
                            value = 0  # Clear RGB when using color wheel
                        else:
                            value = int(g * rgb_scale)
                    elif ch_type == 'blue':
                        # Set RGB to 0 if using color wheel to prevent color mixing
                        if has_color_wheel and fixture_color_wheel_value >= 0:
                            value = 0  # Clear RGB when using color wheel
                        else:
                            value = int(b * rgb_scale)
                    elif ch_type in ('white', 'cool_white', 'warm_white'):
                        value = int(min(r, g, b) * rgb_scale)
                    elif ch_type == 'color_wheel':
                        # Set color wheel if explicitly configured (>=0)
                        # If not using color wheel (-1), reset to 0 (open/white) to prevent
                        # previous preset's color wheel value from affecting RGB colors
                        if fixture_color_wheel_value >= 0:
                            value = fixture_color_wheel_value
                        else:
                            value = 0  # Reset to open/white position when using RGB
                    elif ch_type == 'effect':
                        # Set effect channel if explicitly configured (>=0)
                        # If not set (-1), leave the channel untouched so that
                        # fixture-panel effect buttons / direct DMX writes persist
                        if effect_channel_value >= 0:
                            value = effect_channel_value
                        else:
                            continue  # Don't overwrite user's fixture effect selection
                    elif ch_type == 'shutter':
                        # Shutter channel behavior:
                        # - If fixture has a separate dimmer channel, shutter should be "open" (255) when lit
                        # - But close the shutter (0) when intensity is very low (< 2%) to properly cut light
                        # - If no dimmer channel, shutter acts as dimmer (0-255 range)
                        shutter_threshold = 0.02  # Close shutter below 2% intensity
                        if has_dimmer:
                            # Open shutter when lit, close when intensity is very low
                            value = 255 if intensity_scale > shutter_threshold else 0
                        else:
                            # Shutter as dimmer - close when very low
                            if intensity_scale <= shutter_threshold:
                                value = 0  # Fully closed
                            else:
                                # Map intensity to shutter range
                                min_shutter = 51  # ~20% brightness
                                max_shutter = 255
                                value = int(min_shutter + (max_shutter - min_shutter) * intensity_scale)
                    elif ch_type == 'pan':
                        if skip_pan_tilt:
                            continue
                        if pan is not None:
                            value = pan
                        elif fixture.home_pan is not None:
                            value = fixture.home_pan
                        else:
                            value = 128
                    elif ch_type == 'tilt':
                        if skip_pan_tilt:
                            continue
                        if tilt is not None:
                            value = tilt
                        elif fixture.home_tilt is not None:
                            value = fixture.home_tilt
                        else:
                            value = 128
                    elif ch_type in ('pan_fine', 'tilt_fine'):
                        if skip_pan_tilt:
                            continue
                        value = 0
                    elif ch_type in ('pan_tilt_speed', 'pantilt_speed', 'pt_speed'):
                        if skip_pan_tilt:
                            continue
                        value = 0  # Fastest — let software handle interpolation
                    elif ch_type == 'speed':
                        # Generic 'speed' channel - could be animation speed or other uses
                        # Only skip if it's likely pan/tilt speed (fixture has pan/tilt channels)
                        # Otherwise set to 0 to prevent unwanted animations
                        has_pan_tilt = any(ch.type.lower() in ('pan', 'tilt', 'pan_fine', 'tilt_fine') 
                                          for ch in mode.channels)
                        if skip_pan_tilt and has_pan_tilt:
                            # Fixture has pan/tilt and we're skipping - leave speed alone
                            continue
                        # For fixtures without pan/tilt (like LED bars), set speed to 0
                        # to prevent animation effects from running
                        value = 0
                    elif ch_type in ('type', 'macro', 'auto', 'program'):
                        # Only set macro/type if explicitly provided
                        # Otherwise skip to preserve manual settings
                        if macro is not None:
                            value = macro
                        else:
                            continue  # Skip - don't overwrite current macro value
                    elif ch_type == 'gobo':
                        # Only set gobo if explicitly provided and non-zero
                        # Otherwise skip to preserve manual settings
                        # If rotation value is set and no dedicated gobo_rotation channel,
                        # use rotation value on the gobo channel
                        if gobo_rotation is not None and gobo_rotation > 0:
                            mode_obj = fixture.profile.get_mode(fixture.mode_name)
                            has_rot_ch = False
                            if mode_obj:
                                has_rot_ch = any(c.type.lower() in ('gobo_rotation', 'gobo_shake')
                                                 for c in mode_obj.channels)
                            if not has_rot_ch:
                                value = gobo_rotation
                            elif gobo is not None and gobo > 0:
                                value = gobo
                            else:
                                continue
                        elif gobo is not None and gobo > 0:
                            value = gobo
                        else:
                            continue  # Skip - don't overwrite current gobo value
                    elif ch_type == 'gobo2':
                        if gobo2 is not None and gobo2 > 0:
                            value = gobo2
                        else:
                            continue
                    elif ch_type == 'gobo_rotation':
                        if gobo_rotation is not None and gobo_rotation > 0:
                            value = gobo_rotation
                        else:
                            continue
                    elif ch_type in ('gobo_shake',):
                        if gobo_rotation is not None and gobo_rotation > 0:
                            value = gobo_rotation
                        else:
                            continue
                    elif ch_type == 'gobo2_rotation':
                        if gobo2_rotation is not None and gobo2_rotation > 0:
                            value = gobo2_rotation
                        else:
                            continue
                    elif ch_type == 'prism':
                        # Skip prism to preserve manual settings
                        continue
                    elif ch_type == 'strobe':
                        # Skip strobe to preserve manual settings (unless in strobe effect)
                        continue
                    elif ch_type == 'mode':
                        # Skip mode to preserve manual settings
                        continue
                    elif ch_type == 'on_off':
                        # On/Off channel: output on_value when intensity > 0, off_value when 0
                        if intensity_scale > 0:
                            value = getattr(channel, 'on_value', 255)
                        else:
                            value = getattr(channel, 'off_value', 0)
                    else:
                        # For unknown channel types, skip to avoid overwriting
                        continue
                    
                    if _cap_active:
                        _cap_buffer[(fixture.universe, addr)] = (value, ch_type)
                    else:
                        uni.set_channel(addr, value)
                    dmx_output[i+1] = (channel.name, ch_type, addr, value)
            
            # Log DMX output for first fixture only (once per call to apply_static won't spam)
            if os.environ.get('LD_DMX_DEBUG') == '1' and fixture == fixtures[0]:
                print(f"\n[DMX] Fixture: {fixture.label or fixture.profile.name} @ Address {fixture.address}")
                print(f"[DMX] Color requested: {color}, Intensity: {intensity}%")
                for ch_num, (name, ch_type, addr, val) in dmx_output.items():
                    print(f"[DMX]   Ch{ch_num}: {name:20} ({ch_type:12}) DMX{addr:3} = {val:3}")
    
    def _apply_static_with_palette(self, fixtures: list, effect: EffectParameters, skip_pan_tilt: bool = False):
        """Apply a static look with color variety from palette.
        
        Distributes colors from the palette across fixtures so each fixture
        can have a different shade/color, creating more visual interest.
        
        Args:
            fixtures: List of fixtures to apply to
            effect: EffectParameters containing color_palette and other settings
            skip_pan_tilt: If True, don't set pan/tilt channels (for position cycling)
        """
        palette = effect.color_palette
        if not palette:
            # Fallback to single color
            self.apply_static(fixtures, effect.color, effect.intensity, skip_pan_tilt=skip_pan_tilt)
            return
        
        # Group fixtures by type to distribute colors evenly within each type
        fixture_groups = {}
        for fixture in fixtures:
            fixture_type = fixture.profile.name
            if fixture_type not in fixture_groups:
                fixture_groups[fixture_type] = []
            fixture_groups[fixture_type].append(fixture)
        
        print(f"[Palette] Applying {len(palette)}-color palette to {len(fixtures)} fixtures across {len(fixture_groups)} groups")
        for color in palette:
            print(f"[Palette]   Color: {color}")
        
        # Apply colors to each fixture, cycling through palette
        for group_name, group_fixtures in fixture_groups.items():
            print(f"[Palette] Group '{group_name}': {len(group_fixtures)} fixtures")
            for i, fixture in enumerate(group_fixtures):
                # Cycle through palette colors
                color = palette[i % len(palette)]
                fixture_name = fixture.label or fixture.profile.name
                print(f"[Palette]   {fixture_name} -> {color}")
                
                # Apply to individual fixture
                self.apply_static([fixture], color, effect.intensity,
                                color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                skip_pan_tilt=skip_pan_tilt,
                                **self._gobo_kwargs(effect))

    def _apply_position_preset(self, preset_name: str, fixtures: list):
        """Apply a saved position preset to fixtures."""
        # Check if position preview is active - if so, skip ALL pan/tilt changes
        if self._is_preview_active():
            print(f"[Position] Position preview active - skipping position preset '{preset_name}'")
            return
        
        # Find the position preset by name/alias, or by ID
        preset = self.project.get_position_preset_by_id(preset_name)
        if not preset:
            preset = self.project.get_position_preset_by_name(preset_name)
        if not preset:
            print(f"[Position] WARNING: Position preset '{preset_name}' not found")
            return
        
        print(f"[Position] Applying position preset '{preset.name}' to {len(fixtures)} fixtures")
        
        applied_count = 0
        for fixture in fixtures:
            if fixture.id not in preset.fixture_positions:
                continue
            
            pos = preset.fixture_positions[fixture.id]
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = self.artnet.get_universe(fixture.universe)
            if not uni:
                continue
            
            for i, ch in enumerate(mode.channels):
                ch_type = ch.type.lower()
                addr = fixture.address + i  # 1-indexed for Art-Net
                
                if ch_type == 'pan' and 'pan' in pos:
                    uni.set_channel(addr, pos['pan'])
                    print(f"[Position]   {fixture.label or fixture.profile.name}: Pan = {pos['pan']}")
                elif ch_type == 'tilt' and 'tilt' in pos:
                    uni.set_channel(addr, pos['tilt'])
                    print(f"[Position]   {fixture.label or fixture.profile.name}: Tilt = {pos['tilt']}")
            
            applied_count += 1
        
        print(f"[Position] Applied position to {applied_count} fixtures")

    def _buffer_position_preset(self, buffer: dict, preset_name: str, fixtures: list):
        """Write position preset pan/tilt values into *buffer* (not Art-Net).

        This ensures the HTP merge loop re-outputs the values every frame,
        preventing them from being overwritten.
        """
        # Find the position preset by ID first, then by name
        preset = self.project.get_position_preset_by_id(preset_name)
        if not preset:
            preset = self.project.get_position_preset_by_name(preset_name)
        if not preset:
            return

        for fixture in fixtures:
            if fixture.id not in preset.fixture_positions:
                continue

            pos = preset.fixture_positions[fixture.id]
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue

            for i, ch in enumerate(mode.channels):
                ch_type = ch.type.lower()
                addr = fixture.address + i

                if ch_type == 'pan' and 'pan' in pos:
                    buffer[(fixture.universe, addr)] = (pos['pan'], ch_type)
                elif ch_type == 'tilt' and 'tilt' in pos:
                    buffer[(fixture.universe, addr)] = (pos['tilt'], ch_type)

    def update_effect(self, effect: EffectParameters):
        """Update effect parameters without restarting the cycle.
        
        This preserves the current phase/position in the animation.
        Only updates if an effect is already running.
        """
        print(f"[update_effect] Called with effect_type='{effect.effect_type}', intensity={effect.intensity}")
        
        if not self._running or not self._current_effect:
            # No effect running, just start a new one
            print(f"[update_effect] No effect running, starting new one")
            self.start_effect(effect)
            return
        
        print(f"[update_effect] Current running effect_type='{self._current_effect.effect_type}'")
        
        # Check if effect type changed - if so, need full restart
        if effect.effect_type != self._current_effect.effect_type:
            print(f"[Effect] Effect type changed from {self._current_effect.effect_type} to {effect.effect_type}, restarting")
            self.start_effect(effect)
            return
        
        # Check if target groups changed - if so, need full restart
        if effect.target_groups != self._current_effect.target_groups:
            print(f"[Effect] Target groups changed, restarting")
            self.start_effect(effect)
            return
        
        # Check if position cycling was toggled - need to restart to start/stop the thread
        old_position_cycle = getattr(self._current_effect, 'position_cycle_enabled', False)
        new_position_cycle = getattr(effect, 'position_cycle_enabled', False)
        if old_position_cycle != new_position_cycle:
            print(f"[Effect] Position cycling changed from {old_position_cycle} to {new_position_cycle}, restarting")
            self.start_effect(effect)
            return
        
        # Check if movement pattern was added to static effect BEFORE updating
        old_has_movement = (getattr(self._current_effect, 'movement_pattern', '') or '').lower() not in ('none', '')
        new_has_movement = (getattr(effect, 'movement_pattern', '') or '').lower() not in ('none', '')
        
        # Update the current effect parameters in place
        # The running thread will pick up these changes
        self._current_effect.color = effect.color
        self._current_effect.color_name = effect.color_name
        self._current_effect.intensity = effect.intensity
        self._current_effect.intensity_min = effect.intensity_min
        self._current_effect.intensity_max = effect.intensity_max
        self._current_effect.speed_bpm = effect.speed_bpm
        self._current_effect.direction = effect.direction
        self._current_effect.movement_pattern = effect.movement_pattern
        self._current_effect.cycle_seconds = effect.cycle_seconds
        self._current_effect.pan_min = effect.pan_min
        self._current_effect.pan_max = effect.pan_max
        self._current_effect.tilt_min = effect.tilt_min
        self._current_effect.tilt_max = effect.tilt_max
        self._current_effect.rainbow_colors = effect.rainbow_colors
        self._current_effect.color_palette = getattr(effect, 'color_palette', [])
        self._current_effect.color_wheel_value = getattr(effect, 'color_wheel_value', -1)
        self._current_effect.gobo_value = getattr(effect, 'gobo_value', 0)
        self._current_effect.gobo_rotation_value = getattr(effect, 'gobo_rotation_value', 0)
        self._current_effect.gobo2_value = getattr(effect, 'gobo2_value', 0)
        self._current_effect.gobo2_rotation_value = getattr(effect, 'gobo2_rotation_value', 0)
        self._current_effect.fixture_offset = getattr(effect, 'fixture_offset', 0.25)
        # Position cycling parameters
        self._current_effect.position_cycle_enabled = getattr(effect, 'position_cycle_enabled', False)
        self._current_effect.position_cycle_presets = getattr(effect, 'position_cycle_presets', [])
        self._current_effect.position_cycle_hold_time = getattr(effect, 'position_cycle_hold_time', 4.0)
        self._current_effect.position_cycle_speed = getattr(effect, 'position_cycle_speed', 0)
        
        logger.debug(f"[EffectEngine] update_effect: intensity={self._current_effect.intensity}%, color={self._current_effect.color}")
        print(f"[Effect] Updated parameters: color={effect.color}, intensity={effect.intensity}%, speed={effect.speed_bpm}BPM, pattern={effect.movement_pattern}")
        
        # If movement pattern was ADDED to a static effect with no thread, start a thread
        if effect.effect_type == 'static' and new_has_movement and not old_has_movement:
            if self._thread is None or not self._thread.is_alive():
                print(f"[Effect] Movement pattern added to static effect: {effect.movement_pattern}")
                print(f"[Effect] Starting animation thread for static+movement")
                fixtures = self.get_target_fixtures(effect)
                self._safe_start_thread(self._run_effect_loop, (effect, fixtures), "static+movement")
                return
        
        # For static effects without a running thread, we need to re-apply immediately
        # since there's no loop to pick up the changes
        if effect.effect_type == 'static' and (self._thread is None or not self._thread.is_alive()):
            fixtures = self.get_target_fixtures(effect)
            if fixtures:
                if effect.color_palette and len(effect.color_palette) > 0:
                    self._apply_static_with_palette(fixtures, effect, skip_pan_tilt=True)
                else:
                    self.apply_static(fixtures, effect.color, effect.intensity,
                                    color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                    effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                    skip_pan_tilt=True,
                                    **self._gobo_kwargs(effect))
                logger.debug(f"[EffectEngine] Re-applied static effect with intensity={effect.intensity}%")

    def start_effect(self, effect: EffectParameters):
        """Start running an effect."""
        # Preserve fader level before stopping (stop_effect resets it to 1.0)
        preserved_fader_level = getattr(self, '_fader_level', 1.0)
        
        # Stop previous effect without blackout - we're transitioning to a new effect
        # The new effect will immediately set the correct colors
        self.stop_effect(blackout=False, send_home=False)
        
        # Restore fader level after stop (prevents flash to full brightness when using MIDI faders)
        self._fader_level = preserved_fader_level
        
        # Clear pixel fixture dimmer cache at start of new effect
        if hasattr(self, '_pixel_fixture_dimmers_set'):
            self._pixel_fixture_dimmers_set.clear()
        
        self._current_effect = effect
        self._effect_start_time = time.time()
        self._stop_event.clear()
        self._running = True
        
        # Log what we received
        print(f"[Effect] Received effect: type={effect.effect_type}, target_groups={effect.target_groups}, target_fixtures={effect.target_fixtures}")
        print(f"[Effect] movement_pattern={effect.movement_pattern}, color={effect.color}")
        print(f"[Effect] position_cycle_enabled={getattr(effect, 'position_cycle_enabled', False)}, position_cycle_presets={getattr(effect, 'position_cycle_presets', [])}")
        
        # Get target fixtures - sort by position for chase/wave effects (left-to-right ordering)
        sort_by_position = (effect.effect_type in ('chase', 'rainbow')
                            or effect.effect_type.startswith('geo_')
                            or effect.effect_type.startswith('pixel_'))
        fixtures = self.get_target_fixtures(effect, sort_by_position=sort_by_position)
        print(f"[Effect] Starting {effect.effect_type} on {len(fixtures)} fixtures")
        print(f"[Effect] Color: {effect.color}, Color Name: {effect.color_name}, Intensity: {effect.intensity}%")
        
        # If targeting a subset of fixtures, blackout the non-targeted ones
        # This prevents leftover DMX values from a previous "all" effect being visible
        if len(fixtures) < len(self.project.fixtures):
            targeted_ids = {id(f) for f in fixtures}
            non_targeted = [f for f in self.project.fixtures if id(f) not in targeted_ids]
            if non_targeted:
                print(f"[Effect] Blacking out {len(non_targeted)} non-targeted fixtures")
                self._blackout_fixtures(non_targeted)
        
        # Apply position preset if specified.
        # When a movement pattern or position cycling is active, do NOT snap
        # pan/tilt immediately — the effect loop's ramp-in system will capture
        # the current position and smoothly transition over 2 seconds.
        position_preset_name = getattr(effect, 'position_preset', '')
        _has_movement_early = effect.movement_pattern and effect.movement_pattern.lower() not in ('none', '')
        _has_cycling_early = getattr(effect, 'position_cycle_enabled', False)
        if position_preset_name and not _has_movement_early and not _has_cycling_early:
            self._apply_position_preset(position_preset_name, fixtures)
        elif position_preset_name:
            print(f"[Effect] Deferring position preset '{position_preset_name}' — ramp-in will handle smooth transition")
        
        # Log fixture color wheel lookup - what DMX value will be sent?
        first_fixture = True
        for fixture in fixtures:
            mode = fixture.profile.get_mode(fixture.mode_name)
            if mode:
                for ch in mode.channels:
                    if ch.type.lower() == 'color_wheel' and ch.color_wheel_colors:
                        dmx_val, color_name = find_closest_color_wheel_value(effect.color, ch.color_wheel_colors)
                        print(f"[Effect] {fixture.label or fixture.profile.name}: {effect.color} -> {color_name} = DMX {dmx_val}")
                        if first_fixture:
                            print(f"[Effect]   Available colors: {[(c['name'], c['value']) for c in ch.color_wheel_colors]}")
                            first_fixture = False
                        break
        
        if not fixtures:
            print("[Effect] WARNING: No fixtures to apply effect to!")
            return
        
        # Check if position cycling is enabled
        position_cycling = getattr(effect, 'position_cycle_enabled', False)
        
        # Check if movement pattern is set (animation required)
        has_movement_pattern = effect.movement_pattern and effect.movement_pattern.lower() not in ('none', '')
        print(f"[Effect] has_movement_pattern check: movement_pattern={repr(effect.movement_pattern)}, has_movement_pattern={has_movement_pattern}")
        
        # Check if we should reset movers to home position (when loading presets without movement)
        reset_to_home = getattr(effect, 'reset_to_home', False)
        
        if effect.effect_type == 'static' and not position_cycling and not has_movement_pattern:
            # Static effect with NO movement and NO position cycling
            # We still need a thread to monitor fader level changes for MIDI control
            # Always send movers to their home positions when not doing movement
            skip_pan_tilt = False  # Don't skip - we want to set pan/tilt to home
            
            print(f"[Effect] Static effect without movement - sending movers to home positions")
            # Send moving heads to home before applying the effect (only targeted fixtures)
            self._send_fixtures_home(fixtures)
            
            # Check if we have a color palette for variety
            if effect.color_palette and len(effect.color_palette) > 0:
                self._apply_static_with_palette(fixtures, effect, skip_pan_tilt=skip_pan_tilt)
                print(f"[Effect] Applied static effect with {len(effect.color_palette)}-color palette (movers at home)")
            else:
                self.apply_static(fixtures, effect.color, effect.intensity, 
                                color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                skip_pan_tilt=skip_pan_tilt,
                                **self._gobo_kwargs(effect))
                print(f"[Effect] Applied static effect (movers at home)")
            
            # Start a fader monitor thread to respond to MIDI fader changes
            self._safe_start_thread(self._run_static_fader_monitor, (effect, fixtures, skip_pan_tilt), "fader monitor")
        elif effect.effect_type == 'static' and has_movement_pattern and position_cycling:
            # Static WITH BOTH movement pattern AND position cycling
            print(f"[Effect] Starting static effect with BOTH movement pattern AND position cycling")
            print(f"[Effect]   Movement: {effect.movement_pattern} at {effect.speed_bpm} BPM")
            print(f"[Effect]   Position cycling: enabled")
            
            # Apply static effect immediately (color/intensity), skipping pan/tilt
            if effect.color_palette and len(effect.color_palette) > 0:
                self._apply_static_with_palette(fixtures, effect, skip_pan_tilt=True)
            else:
                self.apply_static(fixtures, effect.color, effect.intensity, 
                                color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                skip_pan_tilt=True,
                                **self._gobo_kwargs(effect))
            
            # Start animation thread - will apply movement pattern (takes precedence)
            self._safe_start_thread(self._run_effect_loop, (effect, fixtures), "static+movement+position")
        elif effect.effect_type == 'static' and has_movement_pattern:
            # Static WITH movement pattern - needs a thread for animation
            print(f"[Effect] Starting static effect WITH movement pattern: {effect.movement_pattern}")
            print(f"[Effect]   Movement speed: {effect.speed_bpm} BPM")
            
            # Apply static effect immediately (color/intensity), skipping pan/tilt
            if effect.color_palette and len(effect.color_palette) > 0:
                self._apply_static_with_palette(fixtures, effect, skip_pan_tilt=True)
            else:
                self.apply_static(fixtures, effect.color, effect.intensity, 
                                color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                skip_pan_tilt=True,
                                **self._gobo_kwargs(effect))
            
            # Start animation thread for continuous pan/tilt movement
            self._safe_start_thread(self._run_effect_loop, (effect, fixtures), "static+movement")
        elif effect.effect_type == 'static' and position_cycling:
            # Static WITH position cycling needs a thread to cycle positions
            print(f"[Effect] Starting static effect with position cycling")
            print(f"[Effect]   position_cycle_presets: {effect.position_cycle_presets}")
            print(f"[Effect]   position_cycle_hold_time: {getattr(effect, 'position_cycle_hold_time', 4.0)}")
            print(f"[Effect]   fader_level: {getattr(self, '_fader_level', 'NOT_SET')} (1.0=button, <1.0=fader)")
            
            # Apply static effect immediately (color/intensity), skipping pan/tilt
            if effect.color_palette and len(effect.color_palette) > 0:
                self._apply_static_with_palette(fixtures, effect, skip_pan_tilt=True)
            else:
                self.apply_static(fixtures, effect.color, effect.intensity, 
                                color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                skip_pan_tilt=True,
                                **self._gobo_kwargs(effect))
            
            # Set pan_tilt_speed for position cycling (actual pan/tilt ramp-in is handled by the effect loop)
            preset_ids = effect.position_cycle_presets
            if preset_ids and len(preset_ids) > 0:
                first_preset_id = preset_ids[0]
                first_preset = next((p for p in self.project.position_presets if p.id == first_preset_id), None)
                if first_preset:
                    print(f"[Effect] Initial position '{first_preset.name}' will ramp in smoothly")
                    speed = getattr(effect, 'position_cycle_speed', 0)
                    for fixture in fixtures:
                        mode = fixture.mode
                        if not mode:
                            continue
                        uni = self.artnet.get_universe(fixture.universe)
                        for i, ch in enumerate(mode.channels):
                            if ch.type.lower() in ('pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'speed'):
                                uni.set_channel(fixture.address + i, speed)
            
            # Now start the thread to cycle positions
            self._safe_start_thread(self._run_effect_loop, (effect, fixtures), "static+position_cycling")
        elif effect.effect_type == 'random':
            # Random sets random DMX values to all channels (grouped fixtures get same values)
            # Always send movers home when there's no movement pattern
            if not has_movement_pattern:
                print(f"[Effect] Random effect without movement - sending movers to home position")
                self._send_fixtures_home(fixtures)
            self.apply_random(fixtures, effect)
            print(f"[Effect] Applied random effect to {len(fixtures)} fixtures")
        elif effect.effect_type == 'macro':
            # Macro sets type channel once, then holds
            # Always send movers home when there's no movement pattern
            if not has_movement_pattern:
                print(f"[Effect] Macro effect without movement - sending movers to home position")
                self._send_fixtures_home(fixtures)
            self._apply_macro(fixtures, effect)
            print(f"[Effect] Applied macro effect (value={effect.macro_value})")
        elif effect.effect_type == 'position_cycle':
            # Position cycle - needs thread to cycle through position presets
            if not self.project.position_presets:
                print("[Effect] WARNING: No position presets defined! Create some in the Positions tab.")
                # Fall back to sweep movement
                effect.effect_type = 'movement'
                effect.movement_pattern = 'sweep'
                self._safe_start_thread(self._run_effect_loop, (effect, fixtures), "fallback_sweep")
            else:
                if self._safe_start_thread(self._run_position_cycle_loop, (effect, fixtures), "position_cycle"):
                    print(f"[Effect] Started position cycle with {len(self.project.position_presets)} presets")
        else:
            # Start effect thread for animated effects (fade, pulse, rainbow, strobe, etc.)
            
            # Always send movers home when there's no movement pattern and no position cycling
            # This ensures movers return home when switching from a mover effect to a non-mover effect
            if not has_movement_pattern and not position_cycling:
                print(f"[Effect] Animated effect without movement - sending movers to home position")
                self._send_fixtures_home(fixtures)
            
            # Set pan_tilt_speed for position cycling (actual pan/tilt ramp-in is handled by the effect loop)
            if position_cycling:
                preset_ids = effect.position_cycle_presets
                if preset_ids and len(preset_ids) > 0:
                    first_preset_id = preset_ids[0]
                    first_preset = next((p for p in self.project.position_presets if p.id == first_preset_id), None)
                    if first_preset:
                        print(f"[Effect] Initial position '{first_preset.name}' will ramp in smoothly")
                        speed = getattr(effect, 'position_cycle_speed', 0)
                        for fixture in fixtures:
                            mode = fixture.mode
                            if not mode:
                                continue
                            uni = self.artnet.get_universe(fixture.universe)
                            for i, ch in enumerate(mode.channels):
                                if ch.type.lower() in ('pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'speed'):
                                    uni.set_channel(fixture.address + i, speed)
            
            if not self._safe_start_thread(self._run_effect_loop, (effect, fixtures), "effect loop"):
                # Fallback to synchronous static application
                print(f"[Effect] Falling back to synchronous static application")
                self._apply_static_effect(effect, fixtures)
        
        # Notify callback that effect started
        if self._on_effect_state_change:
            try:
                self._on_effect_state_change("started", effect)
            except Exception as e:
                print(f"[Effect] Error in effect state change callback: {e}")
    
    def stop_effect(self, blackout: bool = True, send_home: bool = False):
        """Stop the current effect.
        
        Args:
            blackout: If True, turn off all lights after stopping. Default True.
            send_home: If True, send moving heads to home positions. Default False.
        """
        self._running = False
        # NOTE: _execute_mode is NOT cleared here.  start_effect() preserves
        # and restores it, but clearing here opens a race window where the
        # overlay timer can see _execute_mode==False and re-claim channels
        # before the new effect starts.  Callers that truly stop (not restart)
        # must clear _execute_mode explicitly.
        self._stop_event.set()
        if self._thread and self._thread.is_alive():
            self._thread.join(timeout=0.05)
        self._thread = None
        self._current_effect = None
        self._fader_level = 1.0  # Reset fader level when stopping
        
        # Handle post-stop actions
        if send_home:
            self._send_fixtures_home()
        
        # Always blackout if requested (even when send_home is True)
        if blackout:
            self.blackout()
        
        # Notify callback that effect stopped
        if self._on_effect_state_change:
            try:
                self._on_effect_state_change("stopped", None)
            except Exception as e:
                print(f"[Effect] Error in effect state change callback: {e}")
    
    # =========================================================================
    # HTP Multi-Effect Blending Methods
    # =========================================================================
    
    def start_effect_htp(self, preset_id: str, effect: EffectParameters, fader_level: float = 1.0,
                          fade_in_time: float = 0.0, fade_out_time: float = 0.0,
                          effect_duration: float = 0.0, reverse: bool = False):
        """Start an effect with HTP blending support.
        
        Multiple effects can run simultaneously. Their outputs are merged using:
        - HTP (Highest Takes Precedence) for intensity/dimmer channels
        - Highest fader level wins for position (pan/tilt) and discrete channels (gobo, color wheel)
        
        Args:
            preset_id: Unique identifier for this effect (usually the preset ID)
            effect: Effect parameters
            fader_level: Initial fader level 0.0-1.0 (default 1.0)
            fade_in_time: Fade-in duration in seconds (0 = use default 0.3s)
            fade_out_time: Fade-out duration in seconds before effect ends
            effect_duration: Total effect duration in seconds (0 = infinite)
            reverse: Reverse animation direction
        """
        # If this preset is already running, update its parameters and fader level
        if preset_id in self._active_effects:
            active = self._active_effects[preset_id]
            # Update intensity if it changed (allows per-segment intensity control)
            if active.effect.intensity != effect.intensity:
                print(f"[HTP] Updating effect intensity for {preset_id[:8]}... ({active.effect.intensity} -> {effect.intensity})")
                active.effect.intensity = effect.intensity
            self.set_effect_fader_level(preset_id, fader_level)
            return
        
        print(f"[HTP] Starting effect for preset {preset_id} at fader level {fader_level:.0%}")
        
        # Check if a related effect (same base preset, different segment) is already running
        # If so, start at full brightness to avoid fade-in disruption (continuous effect)
        extract_base_preset = lambda pid: '_'.join(pid.split('_')[1:]) if '_' in pid else pid
        base_preset = extract_base_preset(preset_id)
        skip_fade_in = any(
            extract_base_preset(active_id) == base_preset
            for active_id in list(self._active_effects.keys())
        )
        
        # Create new active effect with fade parameters
        active = ActiveEffect(preset_id, effect, fader_level, 
                              fade_in_time=fade_in_time, fade_out_time=fade_out_time,
                              effect_duration=effect_duration, reverse=reverse)
        if skip_fade_in:
            active.fade_in_progress = 1.0  # Start at full brightness
            print(f"[HTP] New effect - continuous from existing effect, skipping fade-in")
        else:
            fade_in_desc = f"{active.fade_in_duration:.1f}s" if active.fade_in_duration > 0 else "none"
            fade_out_desc = f"{fade_out_time:.1f}s" if fade_out_time > 0 else "none"
            print(f"[HTP] New effect - fade-in: {fade_in_desc}, fade-out: {fade_out_desc}, duration: {effect_duration:.1f}s, reverse: {reverse}")
        self._active_effects[preset_id] = active
        
        # Get target fixtures
        sort_by_position = (effect.effect_type in ('chase', 'rainbow')
                            or effect.effect_type.startswith('geo_')
                            or effect.effect_type.startswith('pixel_'))
        fixtures = self.get_target_fixtures(effect, sort_by_position=sort_by_position)
        
        if not fixtures:
            print(f"[HTP] WARNING: No fixtures for effect {preset_id}")
            return
        
        # Apply position preset if specified (for static positions only).
        # When a movement pattern or position cycling is active, defer to
        # the HTP animation thread's ramp-in for smooth pan/tilt transition.
        position_preset_name = getattr(effect, 'position_preset', '')
        position_cycling = getattr(effect, 'position_cycle_enabled', False)
        has_movement = effect.movement_pattern and effect.movement_pattern.lower() not in ('none', '')
        if position_preset_name and not has_movement and not position_cycling:
            print(f"[HTP] Applying position preset: {position_preset_name}")
            self._apply_position_preset(position_preset_name, fixtures)
        elif position_preset_name:
            print(f"[HTP] Deferring position preset '{position_preset_name}' — ramp-in will handle smooth transition")
        
        # Check if we need an animation thread
        needs_animation = effect.effect_type not in ('static',) or position_cycling or has_movement
        
        if needs_animation or effect.effect_type in ('pulse', 'chase', 'strobe', 'fade', 'rainbow', 'movement'):
            # Start effect thread
            active.stop_event.clear()
            active.thread = Thread(
                target=self._run_htp_effect_loop,
                args=(active, fixtures),
                daemon=True
            )
            active.thread.start()
            print(f"[HTP] Started animation thread for {preset_id}")
        else:
            # Static effect - apply once to buffer
            self._apply_effect_to_buffer(active, fixtures)
        
        # Start merge loop if not running
        self._ensure_merge_loop_running()
        
        # Also set as current effect for backwards compatibility
        self._current_effect = effect
        self._running = True
        
        # Notify callback if this is the first effect starting
        if len(self._active_effects) == 1 and self._on_effect_state_change:
            try:
                self._on_effect_state_change("started", effect)
            except Exception as e:
                print(f"[Effect] Error in effect state change callback: {e}")

    def _reset_orphaned_channels(self, removed_buffer: dict) -> None:
        """Zero (or home) channels a just-removed effect was writing that no
        remaining active effect covers.

        Without this, overlapping or back-to-back effects can leave a light
        stuck on: when one effect ends while another keeps the merge loop
        alive, the ended effect's uncovered channels are never cleared.
        `removed_buffer` maps (universe, addr) -> (value, ch_type).
        """
        if not removed_buffer:
            return
        removed_channels = set(removed_buffer.keys())
        covered = set()
        for remaining in list(self._active_effects.values()):
            try:
                covered.update(remaining.dmx_buffer.keys())
            except RuntimeError:
                pass
        orphaned = removed_channels - covered
        home_fixture_ids = set()
        for (uni, addr) in orphaned:
            if self._check_overlay_channel(uni, addr):
                continue
            ch_type = ''
            buf_val = removed_buffer.get((uni, addr))
            if buf_val and isinstance(buf_val, tuple) and len(buf_val) >= 2:
                ch_type = buf_val[1]
            if ch_type in ('pan', 'tilt', 'pan_fine', 'tilt_fine'):
                for f in self.project.fixtures:
                    if f.universe == uni:
                        mode = f.profile.get_mode(f.mode_name) if f.profile else None
                        if mode and f.address <= addr < f.address + len(mode.channels):
                            home_fixture_ids.add(f.id)
                            break
            else:
                universe = self.artnet.get_universe(uni)
                if universe:
                    universe.set_channel(addr, 0)
        if home_fixture_ids:
            home_fixtures = [f for f in self.project.fixtures if f.id in home_fixture_ids]
            if home_fixtures:
                self._send_fixtures_home(home_fixtures)

    def stop_effect_htp(self, preset_id: str, hold: bool = False, skip_blackout: bool = False):
        """Stop a specific effect by preset ID.
        
        Args:
            preset_id: The preset ID to stop
            hold: If True, keep current DMX values instead of blacking out
            skip_blackout: If True, don't blackout even when no effects remain 
                          (used during effect transitions)
        """
        if preset_id not in self._active_effects:
            print(f"[HTP] stop_effect_htp MISS: {preset_id[:40]} not in active_effects (have {len(self._active_effects)} active)", flush=True)
            return
        
        active = self._active_effects[preset_id]
        print(f"[HTP] Stopping effect for preset {preset_id} (hold={hold}, skip_blackout={skip_blackout})")
        
        # Capture channels this effect was writing before removal
        try:
            removed_buffer = dict(active.dmx_buffer)  # {(uni, addr): (value, ch_type)}
            removed_channels = set(removed_buffer.keys())
        except Exception:
            removed_buffer = {}
            removed_channels = set()
        
        # Stop the effect's thread
        active.stop_event.set()
        if active.thread and active.thread.is_alive():
            active.thread.join(timeout=0.5)
        
        # Remove from active effects (pop is safe against the race where the
        # effect thread's auto-cleanup already removed it before we got here)
        self._active_effects.pop(preset_id, None)
        
        # Reset orphaned channels (channels no longer covered by any remaining
        # effect) back to 0 so that e.g. removing a gobo layer resets the gobo.
        # Skip channels owned by the visualizer overlay / spatial mapper so
        # their live colour output is not clobbered.
        # For pan/tilt channels, send the fixture to its home position instead
        # of zeroing (avoids leaving movers stuck at their last animated pos).
        if self._active_effects and removed_channels:
            self._reset_orphaned_channels(removed_buffer)
        
        # If no more effects, stop merge loop and optionally blackout
        if not self._active_effects:
            self._stop_merge_loop()
            self._running = False
            self._current_effect = None
            if not hold and not skip_blackout:
                self._send_to_home_positions()
            
            # Notify callback that all effects stopped
            if self._on_effect_state_change:
                try:
                    self._on_effect_state_change("stopped", None)
                except Exception as e:
                    print(f"[Effect] Error in effect state change callback: {e}")
        else:
            # Clear this effect's contribution from output
            self._merge_and_output()
    
    def stop_all_effects_htp(self, blackout: bool = True, go_home: bool = False):
        """Stop all running HTP effects.
        
        Args:
            blackout: If True, turn off all lights after stopping
            go_home: If True, send moving heads to home position after stopping (overrides blackout)
        """
        print(f"[HTP] Stopping all {len(self._active_effects)} effects (blackout={blackout}, go_home={go_home})")
        
        # Snapshot the effects up front. Effect worker threads may auto-remove
        # expired entries from self._active_effects concurrently, so iterating
        # the live dict here would raise "dictionary changed size during
        # iteration". A snapshot also lets us join() threads without holding a
        # lock (which would deadlock against the workers' own cleanup).
        active_snapshot = list(self._active_effects.values())
        
        # Stop all effect threads
        for active in active_snapshot:
            active.stop_event.set()
        
        # Wait for threads — use a short timeout since stop_event is
        # already set; threads typically exit within a few milliseconds.
        for active in active_snapshot:
            if active.thread and active.thread.is_alive():
                active.thread.join(timeout=0.05)
        
        # Clear all
        self._active_effects.clear()
        # Only stop the merge loop if no override faders need re-assertion.
        # Group faders store DMX values that the merge loop re-asserts at
        # 40 fps — stopping the loop would let other writers overwrite them.
        if not self._override_dmx_values:
            self._stop_merge_loop()
        self._running = False
        self._current_effect = None
        
        if go_home:
            # Send moving heads to home position
            print("[HTP] Sending fixtures to home positions")
            self._send_to_home_positions()
        elif blackout:
            # Blackout lights AND send movers home so they don't stay
            # stuck at their last animated position.
            self._send_to_home_positions()
        
        # Notify callback that all effects stopped
        if self._on_effect_state_change:
            try:
                self._on_effect_state_change("stopped", None)
            except Exception as e:
                print(f"[Effect] Error in effect state change callback: {e}")
    
    def set_effect_fader_level(self, preset_id: str, fader_level: float):
        """Update the fader level for a running effect.
        
        Args:
            preset_id: The preset ID
            fader_level: New fader level 0.0-1.0
        """
        if preset_id not in self._active_effects:
            return
        
        active = self._active_effects[preset_id]
        old_level = active.fader_level
        active.fader_level = max(0.0, min(1.0, fader_level))
        
        # Update fader level smoothly (with logging removed for performance)
        
        # If bringing fader up from zero or very low, restart the fade-in
        if old_level <= 0.01 and active.fader_level > 0.01:
            active.fade_in_progress = 0.0
            active.start_time = time.time()
            print(f"[HTP] Restarting fade-in for {preset_id[:8]}... (fader {old_level:.0%} -> {active.fader_level:.0%})")
        
        # DON'T modify effect.intensity or intensity_max - those control the wave pattern shape
        # The fader_level is applied in the merge loop to scale overall brightness
        
        if abs(old_level - active.fader_level) > 0.05:
            print(f"[HTP] Fader level for {preset_id}: {active.fader_level:.0%}")
    
    def get_active_effect_ids(self) -> list[str]:
        """Get list of currently active effect preset IDs."""
        return list(self._active_effects.keys())
    
    def get_merged_dmx_values(self, universe: int) -> dict[int, int]:
        """Get current merged HTP values for a specific universe.
        
        Returns a dict of {channel: value} for the specified universe.
        This allows external callers (like the Player) to merge effect values
        into their own Art-Net packets.
        """
        if not self._active_effects:
            return {}
        
        result = {}
        
        # Collect all DMX values from all effects for this universe
        # Format: {channel: [(value, fader_level, channel_type, preset_id), ...]}
        all_values: dict[int, list] = {}
        current_time = time.time()
        
        for active in list(self._active_effects.values()):
            # Calculate fade multipliers
            elapsed = current_time - active.start_time
            fade_in_mult = min(1.0, elapsed / active.fade_in_duration) if active.fade_in_duration > 0 else 1.0
            fade_out_mult = 1.0
            if active.effect_duration > 0 and active.fade_out_duration > 0:
                time_remaining = active.effect_duration - elapsed
                if time_remaining < active.fade_out_duration:
                    fade_out_mult = max(0.0, time_remaining / active.fade_out_duration)
            combined_fade = fade_in_mult * fade_out_mult
            
            try:
                buffer_snapshot_2 = list(active.dmx_buffer.items())
            except RuntimeError:
                buffer_snapshot_2 = []
            for (uni, ch), (value, ch_type) in buffer_snapshot_2:
                if uni != universe:
                    continue
                
                # Only fade dimmer/intensity channels
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    scaled_value = int(value * active.fader_level * combined_fade)
                else:
                    scaled_value = value
                
                if ch not in all_values:
                    all_values[ch] = []
                all_values[ch].append((scaled_value, active.fader_level, ch_type, active.preset_id))
        
        # Merge using HTP for intensity, most-recent-wins for others
        for ch, contributions in all_values.items():
            ch_type = contributions[0][2] if contributions else 'dimmer'
            
            if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer', 'shutter'):
                # HTP - take maximum
                result[ch] = max(c[0] for c in contributions)
            else:
                # Most recent effect wins
                best_preset_id = contributions[0][3]
                best_start_time = 0
                for value, fader_level, ch_type_inner, preset_id in contributions:
                    if preset_id in self._active_effects:
                        effect_start_time = self._active_effects[preset_id].start_time
                        if effect_start_time > best_start_time:
                            best_start_time = effect_start_time
                            best_preset_id = preset_id
                result[ch] = next((c[0] for c in contributions if c[3] == best_preset_id), contributions[0][0])
        
        return result
    
    def _ensure_merge_loop_running(self):
        """Start the merge loop if not already running."""
        if self._merge_thread and self._merge_thread.is_alive():
            return
        
        self._merge_stop_event.clear()
        try:
            self._merge_thread = Thread(target=self._merge_loop, daemon=True)
            self._merge_thread.start()
            print("[HTP] Started merge loop")
        except TypeError as e:
            print(f"[HTP] Failed to start merge loop thread: {e}")
    
    def _stop_merge_loop(self):
        """Stop the merge loop."""
        self._merge_stop_event.set()
        if self._merge_thread and self._merge_thread.is_alive():
            self._merge_thread.join(timeout=0.5)
        self._merge_thread = None
    
    def _merge_loop(self):
        """Background loop that merges all active effects and outputs DMX."""
        frame_time = 1.0 / 40  # 40fps
        
        while not self._merge_stop_event.is_set():
            loop_start = time.perf_counter()
            
            try:
                self._merge_and_output()
            except Exception as e:
                print(f"[HTP] ERROR in _merge_and_output: {e}", flush=True)
                import traceback
                traceback.print_exc()
            
            # Sleep for remaining frame time
            elapsed = time.perf_counter() - loop_start
            sleep_time = frame_time - elapsed
            if sleep_time > 0:
                time.sleep(sleep_time)
    
    def _merge_and_output(self):
        """Merge all active effects using HTP and output to Art-Net."""
        if not self._active_effects:
            # Even without active effects, re-assert override DMX values
            # so group/programme fader outputs are never lost.
            if self._override_dmx_values:
                self._reassert_override_dmx()
            return
        
        # Build set of channels owned by overridden fixtures.
        # Override faders (both group and prog) write directly to Art-Net via
        # their own effect loop, so the HTP merge must skip those channels to
        # prevent the two threads from fighting (which causes visible flashing).
        override_channels: set = set()
        if self._override_fixtures:
            for fixture_id, fader_id in self._override_fixtures.items():
                fixture = self.project.get_fixture_by_id(fixture_id) if self.project else None
                if fixture and fixture.mode:
                    # Use fixture.mode directly — fixture.profile.get_mode()
                    # can return None when mode_name is stale, which would
                    # leave override_channels incomplete and let the merge
                    # overwrite group-fader values (visible flashing).
                    mode = fixture.mode
                    for i in range(len(mode.channels)):
                        override_channels.add((fixture.universe, fixture.address + i))
        
        # Take a snapshot of active effects to avoid dict mutation during iteration
        active_effects_snapshot = list(self._active_effects.values())
        
        # Update fade-in and fade-out progress for all active effects
        current_time = time.time()
        for active in active_effects_snapshot:
            elapsed = current_time - active.start_time
            
            # Calculate fade-in progress
            if active.fade_in_progress < 1.0:
                active.fade_in_progress = min(1.0, elapsed / active.fade_in_duration)
                print(f"[FADE-IN] Preset {active.preset_id[:8]}: progress={active.fade_in_progress:.2f} (elapsed={elapsed:.2f}s)")
            
            # Calculate fade-out progress (if effect has duration and fade-out time)
            active._fade_out_multiplier = 1.0  # Default: no fade-out
            if active.effect_duration > 0 and active.fade_out_duration > 0:
                time_remaining = active.effect_duration - elapsed
                if time_remaining < active.fade_out_duration:
                    active._fade_out_multiplier = max(0.0, time_remaining / active.fade_out_duration)
                    # Debug fade-out (only print once per second)
                    debug_key = f"_fadeout_debug_{active.preset_id}"
                    last_debug = getattr(self, debug_key, 0)
                    if current_time - last_debug > 0.5:
                        setattr(self, debug_key, current_time)
                        print(f"[FADE-OUT] Preset {active.preset_id[:8]}: {active._fade_out_multiplier:.0%} (remaining={time_remaining:.1f}s)")
        
        # Collect all DMX values from all effects
        # Format: {(universe, channel): [(value, fader_level, channel_type), ...]}
        all_values: dict[tuple, list] = {}
        
        for active in active_effects_snapshot:
            # Snapshot the buffer to avoid RuntimeError if the effect thread
            # calls buffer.clear() while we iterate (race condition).
            try:
                buffer_snapshot = list(active.dmx_buffer.items())
            except RuntimeError:
                buffer_snapshot = []  # dict changed during copy — skip this frame
            for (uni, ch), (value, ch_type) in buffer_snapshot:
                key = (uni, ch)
                # Apply fade-in and fade-out multipliers to intensity channels
                fade_in_mult = active.fade_in_progress
                fade_out_mult = getattr(active, '_fade_out_multiplier', 1.0)
                combined_fade = fade_in_mult * fade_out_mult
                
                # Only fade dimmer/intensity channels - colors switch instantly
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    # Apply fader level, fade-in, and fade-out to brightness
                    scaled_value = int(value * active.fader_level * combined_fade)
                else:
                    scaled_value = value  # RGB, pan, tilt, gobo, etc. - use as-is
                # Include layer_type so the merge can treat dimmer layers specially
                layer_type = getattr(active.effect, 'layer_type', '') or ''
                if key not in all_values:
                    all_values[key] = []
                all_values[key].append((scaled_value, active.fader_level, ch_type, active.preset_id, layer_type))
        
        # Merge and output
        for (uni, ch), contributions in all_values.items():
            # Determine channel type from first contribution
            ch_type = contributions[0][2] if contributions else 'dimmer'

            # Split contributions into normal layers vs dimmer/intensity-overlay layers.
            # Dimmer layers act as a brightness *ceiling* (multiplicative),
            # NOT an additive HTP contributor, so they can actually dim below
            # what a color layer sets.  Intensity layers also act as a ceiling
            # for dimmer channels so saved-look intensity layers correctly limit
            # the color layer's dimmer output via HTP.
            _dimmer_cap_types = {'dimmer', 'intensity'}
            normal = [c for c in contributions if c[4] not in _dimmer_cap_types]
            dimmer_overlay = [c for c in contributions if c[4] in _dimmer_cap_types]

            # HTP for intensity only, most-recent-wins for RGB and discrete channels
            if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer', 'shutter'):
                if normal and dimmer_overlay:
                    # Both exist: dimmer layer caps the normal HTP value
                    normal_max = max(c[0] for c in normal)
                    dimmer_val = min(c[0] for c in dimmer_overlay)
                    final_value = min(normal_max, dimmer_val)
                elif normal:
                    # Only normal layers — classic HTP
                    final_value = max(c[0] for c in normal)
                else:
                    # Only dimmer layer(s) — use as raw value
                    final_value = max(c[0] for c in dimmer_overlay)
            else:
                # RGB, pan, tilt, gobo, color_wheel, etc.
                # Prefer non-dimmer layer contributions.  Winner = highest
                # stack priority (top of the layer list = lowest stack_order);
                # ties fall back to most-recently-started (LTP).
                source = normal if normal else dimmer_overlay
                best_preset_id = source[0][3]
                best_rank = None  # (stack_order, -start_time); smaller wins
                for c in source:
                    preset_id = c[3]
                    ae = self._active_effects.get(preset_id)
                    order = getattr(ae.effect, 'stack_order', 1_000_000) if ae else 1_000_000
                    start_time = ae.start_time if ae else 0.0
                    rank = (order, -start_time)
                    if best_rank is None or rank < best_rank:
                        best_rank = rank
                        best_preset_id = preset_id
                final_value = next((c[0] for c in source if c[3] == best_preset_id), source[0][0])

                # When a dimmer overlay exists alongside a normal layer,
                # modulate RGB/white values by the dimmer brightness ratio.
                # Only pure 'dimmer' layers modulate RGB; 'intensity' layers
                # only cap the dimmer channel (they don't re-scale RGB).
                # Discrete channels (color_wheel, gobo, pan, tilt, etc.)
                # must NOT be scaled — their values are positions, not
                # intensities, and scaling would corrupt them.
                _scalable_by_dimmer = {'red', 'green', 'blue', 'white',
                                       'cool_white', 'warm_white'}
                pure_dimmer = [c for c in contributions if c[4] == 'dimmer']
                if normal and pure_dimmer and ch_type in _scalable_by_dimmer:
                    dimmer_ratio = min(c[0] for c in pure_dimmer) / 255.0
                    final_value = int(final_value * dimmer_ratio)
            
            # Output to Art-Net (skip channels owned by override faders
            # or by the visualizer overlay / spatial mapper)
            if (uni, ch) in override_channels:
                continue
            if self._check_overlay_channel(uni, ch):
                continue

            # Apply per-fixture MASTER DIMMER scaling (group intensity faders
            # and fixture-type caps).  This is the single point that all
            # HTP-routed effects flow through, so doing it here ensures every
            # effect type — layer-stack presets, song-timeline clips, HTP
            # geo/ensemble effects — respects the group master faders.
            # Only scale brightness-bearing channels; positional/discrete
            # channels (pan/tilt/gobo/color_wheel/etc.) must stay untouched.
            if (self._group_intensities or self._fixture_type_caps) and ch_type in (
                'dimmer', 'intensity', 'master', 'master dimmer',
                'red', 'green', 'blue', 'white', 'cool_white', 'warm_white',
                'amber', 'uv'):
                fixture = self._channel_fixture_cache.get((uni, ch))
                if fixture is None and self.project is not None:
                    # Lazy-build a single entry: find the fixture that owns
                    # this (universe, channel) address.
                    for fx in self.project.fixtures:
                        if fx.universe != uni or not fx.mode:
                            continue
                        base = fx.address
                        if base <= ch < base + len(fx.mode.channels):
                            self._channel_fixture_cache[(uni, ch)] = fx
                            fixture = fx
                            break
                if fixture is not None:
                    scale = 1.0
                    if self._group_intensities:
                        scale *= self._get_fixture_group_intensity(fixture)
                    if self._fixture_type_caps:
                        scale *= self._get_fixture_type_cap(fixture)
                    if scale != 1.0:
                        final_value = max(0, min(255, int(final_value * scale)))

            universe = self.artnet.get_universe(uni)
            if universe:
                universe.set_channel(ch, final_value)
        
        # Continuously re-assert stored override DMX values so that group
        # fader commands are never lost — even if a code path we haven't
        # guarded writes to those channels between frames.
        if self._override_dmx_values:
            self._reassert_override_dmx()
    
    def _run_htp_effect_loop(self, active: ActiveEffect, fixtures: list):
        """Effect loop for HTP mode - writes to effect's buffer instead of directly to Art-Net."""
        frame_time = 1.0 / 40  # 40fps
        
        # Track phase for animation
        accumulated_phase = 0.0
        last_frame_time = time.time()
        
        # Capture current pan/tilt for smooth ramp-in.
        # Prefer home positions as the starting point when current DMX is
        # uninitialized (0,0) — this avoids a hard snap from the 0-corner.
        mover_fixtures_htp = [f for f in fixtures if self._fixture_has_pan_tilt(f)]
        htp_start_positions = self._capture_current_pan_tilt(mover_fixtures_htp)
        for _mf in mover_fixtures_htp:
            cur = htp_start_positions.get(_mf.id)
            if cur is None or (cur[0] == 0 and cur[1] == 0):
                # Use home position as start if available, else center (128)
                hp = _mf.home_pan if getattr(_mf, 'home_pan', None) is not None else 128
                ht = _mf.home_tilt if getattr(_mf, 'home_tilt', None) is not None else 128
                htp_start_positions[_mf.id] = (hp, ht)
        htp_ramp_start = time.time()
        if htp_start_positions:
            print(f"[HTP] Captured {len(htp_start_positions)} mover start positions for smooth ramp-in")
        
        # Track the last-seen movement pattern so we can re-capture
        # start positions when the user switches patterns mid-flight.
        effect = active.effect  # initial read
        _last_movement_pattern: str = (effect.movement_pattern or '').lower()

        # Position cycling state
        current_preset_index = 0
        time_at_current_position = 0.0
        
        print(f"[HTP] Effect loop started for {active.preset_id}: {effect.effect_type}")
        
        while not active.stop_event.is_set():
            loop_start = time.perf_counter()
            
            try:
                # Re-read effect params each frame so in-place updates are picked up
                effect = active.effect
                
                # Detect movement pattern changes mid-flight and re-capture
                # start positions so the ramp-in applies from the current
                # position instead of snapping.
                _cur_mvmt = (effect.movement_pattern or '').lower()
                if _cur_mvmt != _last_movement_pattern:
                    _is_new_movement = _cur_mvmt not in ('none', '')
                    _was_movement = _last_movement_pattern not in ('none', '')
                    _last_movement_pattern = _cur_mvmt
                    if _is_new_movement:
                        # Re-capture current positions and reset ramp timer
                        htp_start_positions = self._capture_current_pan_tilt(mover_fixtures_htp)
                        for _mf in mover_fixtures_htp:
                            cur = htp_start_positions.get(_mf.id)
                            if cur is None or (cur[0] == 0 and cur[1] == 0):
                                hp = _mf.home_pan if getattr(_mf, 'home_pan', None) is not None else 128
                                ht = _mf.home_tilt if getattr(_mf, 'home_tilt', None) is not None else 128
                                htp_start_positions[_mf.id] = (hp, ht)
                        htp_ramp_start = time.time()
                        print(f"[HTP] Movement pattern changed to '{_cur_mvmt}', re-captured start positions for ramp-in")
                
                # When paused, skip animation updates but keep the loop alive
                if self._paused:
                    time.sleep(frame_time)
                    last_frame_time = time.time()  # Reset time tracking so we don't jump when resuming
                    continue
            
                # Calculate phase
                current_time = time.time()
                delta_time = current_time - last_frame_time
                
                # Check if effect duration has expired (auto-stop the effect)
                if active.effect_duration > 0:
                    elapsed_since_start = current_time - active.start_time
                    if elapsed_since_start >= active.effect_duration:
                        print(f"[HTP] Effect {active.preset_id[:8]} duration expired ({elapsed_since_start:.1f}s >= {active.effect_duration:.1f}s), auto-stopping")
                        # Signal stop - the effect manager will clean up
                        active.stop_event.set()
                        break
                last_frame_time = current_time
                
                current_bpm = max(1, effect.speed_bpm)
                # Apply BPM slowdown for movement effects (same as main effect loop)
                _has_mvmt = effect.movement_pattern and effect.movement_pattern.lower() not in ('none', '')
                if effect.effect_type == 'movement' or (_has_mvmt and effect.effect_type in ('static',)):
                    effective_bpm = max(2, current_bpm / 10)  # 10x slower for smooth movement
                    cycle_duration = 60.0 / (effective_bpm * self._global_speed_multiplier)
                elif effect.effect_type == 'chase':
                    effective_bpm = max(2, current_bpm / 4)  # 4x slower for chases
                    cycle_duration = 60.0 / (effective_bpm * self._global_speed_multiplier)
                elif effect.effect_type == 'dimmer_fx':
                    # Dimmer effects: slow down for smooth visible fades
                    # At BPM=60 this gives ~4s cycle, BPM=120 gives ~2s
                    effective_bpm = max(2, current_bpm / 4)
                    cycle_duration = 60.0 / (effective_bpm * self._global_speed_multiplier)
                else:
                    cycle_duration = 60.0 / (current_bpm * self._global_speed_multiplier)
                
                phase_increment = delta_time / cycle_duration
                accumulated_phase = (accumulated_phase + phase_increment) % 1.0
                
                # Apply reverse if enabled on this effect instance
                phase = accumulated_phase
                if active.reverse:
                    phase = 1.0 - phase
                
                # Handle position cycling if enabled (but NOT if position preview is active)
                position_cycling = getattr(effect, 'position_cycle_enabled', False)
                position_hold_time = getattr(effect, 'position_cycle_hold_time', 4.0) if position_cycling else 4.0
                if position_cycling and not self._is_preview_active():
                    time_at_current_position += delta_time
                    effective_hold_time = position_hold_time / self._global_speed_multiplier
                    
                    if time_at_current_position >= effective_hold_time:
                        # Move to next position
                        time_at_current_position = 0.0
                        
                        # Get position presets
                        all_position_presets = self.project.position_presets
                        if effect.position_cycle_presets:
                            position_presets = [p for p in all_position_presets if p.id in effect.position_cycle_presets]
                        else:
                            position_presets = all_position_presets
                        
                        if position_presets:
                            current_preset_index = (current_preset_index + 1) % len(position_presets)
                            current_preset = position_presets[current_preset_index]
                            print(f"[HTP] Moving to position: {current_preset.name}")
                            
                            # Apply positions directly to Art-Net (position channels not buffered)
                            mover_fixtures = [f for f in fixtures if self._fixture_has_pan_tilt(f)]
                            htp_ramp = self._get_ramp_in_blend(htp_ramp_start)
                            for fixture in mover_fixtures:
                                if fixture.id not in current_preset.fixture_positions:
                                    continue
                                
                                pos = current_preset.fixture_positions[fixture.id]
                                mode = fixture.profile.get_mode(fixture.mode_name)
                                if not mode:
                                    continue
                                
                                uni = self.artnet.get_universe(fixture.universe)
                                if not uni:
                                    continue
                                
                                # Compute blended pan/tilt for smooth ramp-in
                                target_pan = pos.get('pan', 128)
                                target_tilt = pos.get('tilt', 128)
                                if htp_start_positions and htp_ramp < 1.0:
                                    target_pan, target_tilt = self._blend_pan_tilt(
                                        fixture.id, target_pan, target_tilt,
                                        htp_start_positions, htp_ramp)
                                
                                for i, ch in enumerate(mode.channels):
                                    ch_type = ch.type.lower()
                                    addr = fixture.address + i
                                    
                                    if ch_type == 'pan' and 'pan' in pos:
                                        uni.set_channel(addr, target_pan)
                                    elif ch_type == 'tilt' and 'tilt' in pos:
                                        uni.set_channel(addr, target_tilt)
                                    elif ch_type in ('pan_fine', 'tilt_fine'):
                                        uni.set_channel(addr, 0)
                                    elif ch_type in ('pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'speed'):
                                        speed = getattr(effect, 'position_cycle_speed', 0)
                                        uni.set_channel(addr, speed)
                
                # Apply effect to buffer (colors, intensity, etc.) using reversed phase if needed
                self._apply_effect_to_buffer(active, fixtures, phase,
                                              movement_start_positions=htp_start_positions,
                                              movement_ramp_start=htp_ramp_start)

            except Exception as e:
                print(f"[HTP] ERROR in effect loop for {active.preset_id}: {e}", flush=True)
                import traceback
                traceback.print_exc()
            
            # Sleep (always, even on error)
            elapsed = time.perf_counter() - loop_start
            sleep_time = frame_time - elapsed
            if sleep_time > 0:
                time.sleep(sleep_time)
        
        print(f"[HTP] Effect loop ended for {active.preset_id}")
        
        # Auto-cleanup: remove from active effects if duration expired
        if active.effect_duration > 0 and active.preset_id in self._active_effects:
            elapsed_since_start = time.time() - active.start_time
            if elapsed_since_start >= active.effect_duration:
                print(f"[HTP] Auto-removing expired effect {active.preset_id[:8]} from active effects")
                # Snapshot the channels this effect drove before clearing so we
                # can reset any that no remaining effect covers (otherwise an
                # overlapping/touching effect leaves this one's lights stuck on).
                removed_buffer = dict(active.dmx_buffer)
                self._active_effects.pop(active.preset_id, None)
                
                # Clear this effect's buffer contribution
                active.dmx_buffer.clear()
                
                # If no more effects, stop merge loop and send fixtures home
                if not self._active_effects:
                    print(f"[HTP] No more active effects, stopping merge loop and sending home")
                    # Keep merge loop alive if override faders need re-assertion
                    if not self._override_dmx_values:
                        self._stop_merge_loop()
                    self._running = False
                    self._send_to_home_positions()
                else:
                    # Other effects still run: clear only the channels they
                    # don't cover so this expired effect doesn't leave lights on.
                    self._reset_orphaned_channels(removed_buffer)
    
    def _apply_effect_to_buffer(self, active: ActiveEffect, fixtures: list, phase: float = 0.0,
                                  movement_start_positions: dict | None = None,
                                  movement_ramp_start: float = 0.0):
        """Apply an effect's output to its DMX buffer (not directly to Art-Net).
        
        Args:
            active: The ActiveEffect instance
            fixtures: Target fixtures
            phase: Animation phase 0.0-1.0
            movement_start_positions: Optional dict from _capture_current_pan_tilt
                for smooth ramp-in from current positions to the movement pattern.
            movement_ramp_start: time.time() when the ramp started.
        """
        effect = active.effect
        # Build into a local dict, then swap atomically so the merge thread
        # never sees a half-written or empty buffer (prevents flicker).
        buffer = {}
        
        # Get intensity (already scaled by fader in the merge step)
        intensity = effect.intensity
        
        # Apply based on effect type
        if effect.effect_type == 'pulse':
            self._buffer_pulse(buffer, fixtures, effect, phase)
        elif effect.effect_type == 'chase':
            self._buffer_chase(buffer, fixtures, effect, phase)
        elif effect.effect_type == 'fade':
            self._buffer_fade(buffer, fixtures, effect, phase)
        elif effect.effect_type == 'strobe':
            self._buffer_strobe(buffer, fixtures, effect, phase, active.start_time)
        elif effect.effect_type == 'rainbow':
            self._buffer_rainbow(buffer, fixtures, effect, phase)
        elif effect.effect_type == 'pixel_chase':
            self._buffer_pixel_chase(buffer, fixtures, effect, phase)
        elif effect.effect_type == 'pixel_rainbow':
            self._buffer_pixel_rainbow(buffer, fixtures, effect, phase)
        elif effect.effect_type == 'pixel_wipe':
            self._buffer_pixel_wipe(buffer, fixtures, effect, phase)
        elif effect.effect_type == 'pixel_snake':
            self._buffer_pixel_snake(buffer, fixtures, effect, phase)
        elif effect.effect_type == 'pixel_rain_drops':
            self._buffer_pixel_rain_drops(buffer, fixtures, effect, phase)
        elif effect.effect_type == 'pixel_sine_wave':
            self._buffer_pixel_sine_wave(buffer, fixtures, effect, phase)
        elif effect.effect_type == 'dimmer_fx':
            self._buffer_dimmer_effect(buffer, fixtures, effect, phase, active.start_time)
        elif effect.effect_type in self._GEO_EFFECT_MAP:
            self._buffer_geo_adapter(buffer, fixtures, effect, phase,
                                     self._GEO_EFFECT_MAP[effect.effect_type])
        elif effect.effect_type.startswith('ensemble_') and (
                hasattr(self, f'_apply_{effect.effect_type}')
                or effect.effect_type in self._ENSEMBLE_METHOD_ALIASES):
            # Ensemble effects animate via their _apply_ensemble_* handlers,
            # captured into the HTP buffer (same look as the preset panel's
            # main-loop dispatch).  Without this they fell through to
            # _buffer_static and rendered as a flat, non-animated colour.
            _ens_method = self._ENSEMBLE_METHOD_ALIASES.get(
                effect.effect_type, f'_apply_{effect.effect_type}')
            self._buffer_ensemble_adapter(buffer, fixtures, effect, phase, _ens_method)
        else:
            # Static or other - apply fixed values
            # If rainbow_colors flag is set on a static layer, route to rainbow buffer
            if getattr(effect, 'rainbow_colors', False):
                self._buffer_rainbow(buffer, fixtures, effect, phase)
            else:
                self._buffer_static(buffer, fixtures, effect)
        
        # Apply movement pattern if specified (applies to all effect types)
        has_movement = effect.movement_pattern and effect.movement_pattern.lower() not in ('none', '')
        if has_movement:
            # Filter to only movers (fixtures with pan/tilt)
            movers = [f for f in fixtures if self._fixture_has_pan_tilt(f)]
            if movers:
                self._buffer_movement(buffer, movers, effect, phase)

                # ── Movement ramp-in blending ─────────────────────────────
                # Smoothly interpolate pan/tilt from the fixture's starting
                # position (captured when the effect began) to the movement
                # pattern's target.  This prevents hard snaps that stress
                # moving-head motors.
                if movement_start_positions:
                    ramp_blend = self._get_ramp_in_blend(movement_ramp_start)
                    if ramp_blend < 1.0:
                        # Build (uni, addr) → fixture_id lookup for pan/tilt channels
                        _addr_to_fid: dict[tuple, str] = {}
                        _addr_ch_type: dict[tuple, str] = {}
                        for f in movers:
                            mode = f.profile.get_mode(f.mode_name)
                            if not mode:
                                continue
                            for ci, ch in enumerate(mode.channels):
                                ct = ch.type.lower()
                                if ct in ('pan', 'tilt'):
                                    key = (f.universe, f.address + ci)
                                    _addr_to_fid[key] = f.id
                                    _addr_ch_type[key] = ct

                        for key in list(buffer):
                            if key not in _addr_to_fid:
                                continue
                            fid = _addr_to_fid[key]
                            if fid not in movement_start_positions:
                                continue
                            target_val = buffer[key][0]
                            ch_t = _addr_ch_type[key]
                            start_pan, start_tilt = movement_start_positions[fid]
                            start_val = start_pan if ch_t == 'pan' else start_tilt
                            blended = int(start_val + (target_val - start_val) * ramp_blend)
                            buffer[key] = (max(0, min(255, blended)), buffer[key][1])

        # Apply position preset to buffer (makes merge loop maintain values)
        position_preset_name = getattr(effect, 'position_preset', '')
        if position_preset_name:
            self._buffer_position_preset(buffer, position_preset_name, fixtures)

        # ── Layer-type channel filtering ──────────────────────────────────
        # Each layer type only owns certain DMX channel types.  Remove
        # anything the layer shouldn't control so it doesn't interfere
        # with other layers during HTP merge.
        layer_type = getattr(effect, 'layer_type', '') or ''
        _LAYER_OWNED_CHANNELS = {
            'color': {'red', 'green', 'blue', 'white', 'cool_white', 'warm_white',
                      'color_wheel', 'dimmer', 'intensity', 'master', 'master dimmer', 'shutter'},
            'effect': {'red', 'green', 'blue', 'white', 'cool_white', 'warm_white',
                       'color_wheel', 'dimmer', 'intensity', 'master', 'master dimmer', 'shutter',
                       'strobe'},
            'pixel': {'red', 'green', 'blue', 'white', 'cool_white', 'warm_white',
                      'dimmer', 'intensity', 'master', 'master dimmer', 'shutter',
                      'on_off', 'strobe'},
            'movement': {'pan', 'tilt', 'pan_fine', 'tilt_fine',
                         'pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'speed'},
            'position': {'pan', 'tilt', 'pan_fine', 'tilt_fine',
                         'pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'speed'},
            'intensity': {'dimmer', 'intensity', 'master', 'master dimmer', 'shutter'},
            'dimmer': {'dimmer', 'intensity', 'master', 'master dimmer', 'shutter'},
            'gobo': {'gobo', 'gobo1', 'gobo2', 'gobo_wheel', 'gobo_rotation', 'gobo_shake', 'gobo2_rotation'},
            'strobe': {'red', 'green', 'blue', 'white', 'cool_white', 'warm_white',
                       'color_wheel', 'dimmer', 'intensity', 'master', 'master dimmer',
                       'shutter', 'strobe'},
            'prism': {'prism', 'prism_rotation', 'prism_rot', 'prism2', 'prism2_rotation'},
            'optics': {'focus', 'zoom', 'frost', 'iris', 'blade'},
            'fx_channel': {'effect'},
            'fx': {'effect', 'macro', 'function', 'control', 'program', 'type', 'auto', 'mode'},
            'smoke': {'fog', 'fan', 'pump', 'motor', 'on_off'},
        }
        owned = _LAYER_OWNED_CHANNELS.get(layer_type)
        if owned is not None:
            # Expand owned set with channels the user explicitly configured
            # (non-default values) so cross-type settings aren't pruned.
            extra: set = set()
            if getattr(effect, 'gobo_value', 0) != 0 or getattr(effect, 'gobo_rotation_value', 0) != 0:
                extra.update({'gobo', 'gobo1', 'gobo2', 'gobo_wheel',
                              'gobo_rotation', 'gobo_shake', 'gobo2_rotation'})
            if getattr(effect, 'gobo2_value', 0) != 0 or getattr(effect, 'gobo2_rotation_value', 0) != 0:
                extra.update({'gobo2', 'gobo2_rotation'})
            if getattr(effect, 'prism_value', 0) != 0 or getattr(effect, 'prism_rotation', 0) != 0:
                extra.update({'prism', 'prism_rotation', 'prism_rot'})
            if getattr(effect, 'prism2_value', 0) != 0 or getattr(effect, 'prism2_rotation', 0) != 0:
                extra.update({'prism2', 'prism2_rotation'})
            if getattr(effect, 'focus_value', -1) >= 0:
                extra.add('focus')
            if getattr(effect, 'zoom_value', -1) >= 0:
                extra.add('zoom')
            if getattr(effect, 'frost_value', 0) != 0:
                extra.add('frost')
            if getattr(effect, 'effect_channel_value', -1) >= 0:
                extra.add('effect')
            if getattr(effect, 'color_wheel_value', -1) >= 0:
                extra.add('color_wheel')
            effective_owned = owned | extra if extra else owned
            # Prune channels this layer doesn't own
            to_remove = [k for k, (v, ch_t) in buffer.items() if ch_t not in effective_owned]
            for k in to_remove:
                del buffer[k]

        # Atomic swap: replace the live buffer in one operation so the merge
        # thread always sees a complete frame (prevents flicker from
        # buffer.clear() exposing an empty dict mid-write).
        active.dmx_buffer = buffer
    
    def _buffer_static(self, buffer: dict, fixtures: list, effect: EffectParameters):
        """Buffer a static effect."""
        # Apply fader level for MIDI fader control
        fader_level = getattr(self, '_fader_level', 1.0)
        intensity_scale = (effect.intensity / 100.0) * fader_level
        color_wheel_value = getattr(effect, 'color_wheel_value', -1)
        
        # Get color palette for variety (assigns different colors to different fixtures)
        color_palette = effect.color_palette if effect.color_palette else [effect.color]
        
        for idx, fixture in enumerate(fixtures):
            # Select color from palette based on fixture index
            fixture_color = color_palette[idx % len(color_palette)]
            r, g, b = hex_to_rgb(fixture_color)
            
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = fixture.universe
            
            # Check if this fixture has a color wheel channel
            has_color_wheel = False
            color_wheel_channel = None
            for ch in mode.channels:
                if ch.type.lower() == 'color_wheel':
                    has_color_wheel = True
                    color_wheel_channel = ch
                    break
            
            # Check if fixture has a dimmer channel
            has_dimmer = any(ch.type.lower() in ('dimmer', 'intensity', 'master', 'master dimmer') 
                           for ch in mode.channels)
            
            # Apply intensity to RGB to match Timeline Editor behavior
            # Timeline Editor always scales RGB by intensity regardless of dimmer presence
            rgb_scale = intensity_scale
            
            # Determine color wheel value for this fixture
            fixture_color_wheel_value = -1
            if color_wheel_value >= 0:
                # Use explicit color wheel value from effect
                fixture_color_wheel_value = color_wheel_value
            elif has_color_wheel and color_wheel_channel and color_wheel_channel.color_wheel_colors:
                # Look up color wheel value from the fixture's color
                fixture_color_wheel_value, matched_color_name = find_closest_color_wheel_value(
                    fixture_color, color_wheel_channel.color_wheel_colors
                )
            
            # Auto-promote second gobo channel to gobo2 (mirrors _get_fixture_capabilities)
            _gobo_count = 0
            _gobo_rot_count = 0
            for i, channel in enumerate(mode.channels):
                ch_type = channel.type.lower()
                if ch_type == 'gobo' and hasattr(channel, 'gobo_slots') and channel.gobo_slots:
                    _gobo_count += 1
                    if _gobo_count >= 2:
                        ch_type = 'gobo2'
                elif ch_type in ('gobo_rotation', 'gobo_shake'):
                    _gobo_rot_count += 1
                    if _gobo_rot_count >= 2:
                        ch_type = 'gobo2_rotation'
                addr = fixture.address + i
                
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    # Apply preset's intensity - fader_level will be applied in merge
                    value = int(255 * intensity_scale)
                elif ch_type == 'red':
                    # Set RGB to 0 if using color wheel to prevent color mixing
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        value = 0  # Clear RGB when using color wheel
                    else:
                        value = int(r * rgb_scale)
                elif ch_type == 'green':
                    # Set RGB to 0 if using color wheel to prevent color mixing
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        value = 0  # Clear RGB when using color wheel
                    else:
                        value = int(g * rgb_scale)
                elif ch_type == 'blue':
                    # Set RGB to 0 if using color wheel to prevent color mixing
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        value = 0  # Clear RGB when using color wheel
                    else:
                        value = int(b * rgb_scale)
                elif ch_type in ('white', 'cool_white', 'warm_white'):
                    value = int(min(r, g, b) * rgb_scale)
                elif ch_type == 'color_wheel':
                    # Set color wheel if explicitly configured, otherwise reset to 0
                    if fixture_color_wheel_value >= 0:
                        value = fixture_color_wheel_value
                    else:
                        value = 0  # Reset to open/white when using RGB
                elif ch_type == 'shutter':
                    shutter_override = getattr(effect, 'shutter_value', -1)
                    if shutter_override >= 0:
                        value = shutter_override
                    else:
                        shutter_threshold = 0.02
                        if has_dimmer or has_color_wheel:
                            value = 255 if intensity_scale > shutter_threshold else 0
                        else:
                            if intensity_scale <= shutter_threshold:
                                value = 0
                            else:
                                value = int(51 + (255 - 51) * intensity_scale)
                elif ch_type == 'strobe':
                    value = 0
                elif ch_type == 'effect':
                    ecv = getattr(effect, 'effect_channel_value', -1)
                    value = ecv if ecv >= 0 else 0
                elif ch_type in ('gobo', 'gobo1', 'gobo_wheel'):
                    # If rotation value is set and fixture has no dedicated gobo_rotation channel,
                    # use rotation value on the gobo channel (many fixtures use the same channel
                    # for both selection and rotation at different DMX ranges)
                    gobo_rot = getattr(effect, 'gobo_rotation_value', 0)
                    has_rot_ch = any(c.type.lower() in ('gobo_rotation', 'gobo_shake')
                                     for c in mode.channels)
                    if gobo_rot > 0 and not has_rot_ch:
                        value = gobo_rot
                    else:
                        value = getattr(effect, 'gobo_value', 0)
                elif ch_type == 'gobo2':
                    gobo2_rot = getattr(effect, 'gobo2_rotation_value', 0)
                    # Count gobo_rotation channels — if 2+, second is auto-promoted to gobo2_rotation
                    _rot_ch_count = sum(1 for c in mode.channels
                                        if c.type.lower() in ('gobo_rotation', 'gobo_shake'))
                    has_rot2_ch = _rot_ch_count >= 2
                    if gobo2_rot > 0 and not has_rot2_ch:
                        value = gobo2_rot
                    else:
                        value = getattr(effect, 'gobo2_value', 0)
                elif ch_type == 'gobo_rotation':
                    value = getattr(effect, 'gobo_rotation_value', 0)
                elif ch_type == 'gobo_shake':
                    value = getattr(effect, 'gobo_rotation_value', 0)
                elif ch_type == 'gobo2_rotation':
                    value = getattr(effect, 'gobo2_rotation_value', 0)
                elif ch_type == 'prism':
                    pv = getattr(effect, 'prism_value', 0)
                    if pv > 0:
                        value = pv
                    else:
                        value = 0  # Prism off
                elif ch_type in ('prism_rotation', 'prism_rot'):
                    value = getattr(effect, 'prism_rotation', 0)
                elif ch_type == 'prism2':
                    pv2 = getattr(effect, 'prism2_value', 0)
                    if pv2 > 0:
                        value = pv2
                    else:
                        value = 0  # Prism2 off
                elif ch_type == 'prism2_rotation':
                    value = getattr(effect, 'prism2_rotation', 0)
                elif ch_type == 'focus':
                    fv = getattr(effect, 'focus_value', -1)
                    if fv >= 0:
                        value = fv
                    else:
                        continue  # Preserve existing
                elif ch_type == 'zoom':
                    zv = getattr(effect, 'zoom_value', -1)
                    if zv >= 0:
                        value = zv
                    else:
                        continue  # Preserve existing
                elif ch_type == 'frost':
                    value = getattr(effect, 'frost_value', 0)
                elif ch_type == 'on_off':
                    value = getattr(channel, 'on_value', 255) if intensity_scale > 0 else getattr(channel, 'off_value', 0)
                elif ch_type in ('pan', 'tilt', 'pan_fine', 'tilt_fine'):
                    # For position layers (or any static effect with a fixed
                    # pan/tilt coordinate), write the value directly.
                    # pan_min==pan_max means "static position at this value".
                    layer_type = getattr(effect, 'layer_type', '') or ''
                    is_static_pan = (effect.pan_min == effect.pan_max)
                    is_static_tilt = (effect.tilt_min == effect.tilt_max)
                    if layer_type == 'position' or (is_static_pan and is_static_tilt
                                                     and (effect.pan_min != 0 or effect.tilt_min != 0)):
                        if ch_type == 'pan':
                            value = effect.pan_min
                        elif ch_type == 'tilt':
                            value = effect.tilt_min
                        elif ch_type == 'pan_fine':
                            value = 0  # Fine channels default to 0 for manual positions
                        elif ch_type == 'tilt_fine':
                            value = 0
                        else:
                            continue
                    else:
                        continue  # Skip position - handled by movement
                elif ch_type in ('pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'speed'):
                    # Use position_cycle_speed if set (e.g. cue light-speed override),
                    # otherwise default to 0 (fastest) for position layers.
                    layer_type = getattr(effect, 'layer_type', '') or ''
                    speed_override = getattr(effect, 'position_cycle_speed', 0)
                    if layer_type == 'position' or speed_override != 0:
                        value = speed_override
                    else:
                        continue  # Skip speed channels
                elif ch_type in ('type', 'macro', 'auto', 'program', 'mode'):
                    mv = getattr(effect, 'macro_value', 0)
                    if mv > 0:
                        value = mv
                    else:
                        continue  # Preserve existing
                elif ch_type in ('fog', 'pump', 'motor'):
                    # Smoke / haze output: respect other_channel_values if set
                    # (from a dedicated Smoke layer), otherwise gate on intensity.
                    other_vals = getattr(effect, 'other_channel_values', None)
                    if other_vals and ch_type in other_vals:
                        value = other_vals[ch_type]
                    else:
                        value = 255 if intensity_scale > 0 else 0
                elif ch_type == 'fan':
                    # Smoke machine fan speed: use other_channel_values if set.
                    other_vals = getattr(effect, 'other_channel_values', None)
                    if other_vals and 'fan' in other_vals:
                        value = other_vals['fan']
                    else:
                        value = 0  # fan off by default
                else:
                    # Check other_channel_values for uncategorized channels
                    other_vals = getattr(effect, 'other_channel_values', None)
                    if other_vals and ch_type in other_vals:
                        value = other_vals[ch_type]
                    else:
                        continue
                
                buffer[(uni, addr)] = (value, ch_type)
    
    def _buffer_pulse(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """Buffer a pulse effect."""
        intensity_range = effect.intensity_max - effect.intensity_min
        raw_intensity = effect.intensity_min + intensity_range * (0.5 + 0.5 * math.sin(phase * 2 * math.pi))
        # Apply fader level for MIDI fader control
        fader_level = getattr(self, '_fader_level', 1.0)
        intensity = raw_intensity * (effect.intensity / 100.0) * fader_level
        intensity_scale = intensity / 100.0
        
        # Get color palette for variety (assigns different colors to different fixtures)
        color_palette = effect.color_palette if effect.color_palette else [effect.color]
        
        for idx, fixture in enumerate(fixtures):
            # Select color from palette based on fixture index
            fixture_color = color_palette[idx % len(color_palette)]
            r, g, b = hex_to_rgb(fixture_color)
            
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = fixture.universe
            
            # Check if this fixture has a color wheel channel
            has_color_wheel = False
            color_wheel_channel = None
            for ch in mode.channels:
                if ch.type.lower() == 'color_wheel':
                    has_color_wheel = True
                    color_wheel_channel = ch
                    break
            
            # Check if fixture has a dimmer channel
            has_dimmer = any(ch.type.lower() in ('dimmer', 'intensity', 'master', 'master dimmer') 
                           for ch in mode.channels)
            
            # Apply intensity to RGB to match Timeline Editor behavior
            rgb_scale = intensity_scale
            
            # For color wheel fixtures: map color to closest wheel position
            fixture_color_wheel_value = -1
            if has_color_wheel and color_wheel_channel and color_wheel_channel.color_wheel_colors:
                fixture_color_wheel_value, matched_color_name = find_closest_color_wheel_value(
                    fixture_color, color_wheel_channel.color_wheel_colors
                )
            
            for i, channel in enumerate(mode.channels):
                ch_type = channel.type.lower()
                addr = fixture.address + i
                
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    # Output pulsed intensity - merge loop will NOT scale (pulse already modulates)
                    value = int(255 * intensity_scale)
                elif ch_type == 'red':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(r * rgb_scale)
                elif ch_type == 'green':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(g * rgb_scale)
                elif ch_type == 'blue':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(b * rgb_scale)
                elif ch_type in ('white', 'cool_white', 'warm_white'):
                    value = int(min(r, g, b) * rgb_scale)
                elif ch_type == 'color_wheel':
                    if fixture_color_wheel_value >= 0:
                        value = fixture_color_wheel_value
                    else:
                        value = 0  # Reset to open/white when using RGB
                elif ch_type == 'shutter':
                    # For pulse effects: close shutter when intensity is at minimum
                    # Use a threshold (2%) to properly close shutter at bottom of pulse
                    shutter_threshold = 0.02  # Close shutter below 2% intensity
                    if has_dimmer or has_color_wheel:
                        value = 255 if intensity_scale > shutter_threshold else 0
                    else:
                        if intensity_scale <= shutter_threshold:
                            value = 0  # Fully closed
                        else:
                            min_shutter = 51
                            max_shutter = 255
                            value = int(min_shutter + (max_shutter - min_shutter) * intensity_scale)
                elif ch_type == 'strobe':
                    value = 0  # No strobing - let dimmer control intensity
                else:
                    continue
                
                buffer[(uni, addr)] = (value, ch_type)
    
    def _buffer_fade(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """Buffer a fade (cross-fade) effect — smooth linear intensity ramp.
        
        Unlike pulse (sinusoidal), fade uses a triangle wave for linear
        fade-in/fade-out.  With a color palette, consecutive fixtures
        cross-fade between adjacent palette colours.
        """
        # Triangle wave: 0→1→0 over one cycle
        tri = 1.0 - abs(2.0 * phase - 1.0)
        intensity_range = effect.intensity_max - effect.intensity_min
        raw_intensity = effect.intensity_min + intensity_range * tri

        fader_level = getattr(self, '_fader_level', 1.0)
        intensity = raw_intensity * (effect.intensity / 100.0) * fader_level
        intensity_scale = intensity / 100.0

        color_palette = effect.color_palette if effect.color_palette else [effect.color]

        for idx, fixture in enumerate(fixtures):
            # Cross-fade between palette colours when multiple
            if len(color_palette) > 1:
                slot = (phase * len(color_palette) + idx * 0.5) % len(color_palette)
                c_idx = int(slot) % len(color_palette)
                c_next = (c_idx + 1) % len(color_palette)
                frac = slot - int(slot)
                r1, g1, b1 = hex_to_rgb(color_palette[c_idx])
                r2, g2, b2 = hex_to_rgb(color_palette[c_next])
                r = int(r1 + (r2 - r1) * frac)
                g = int(g1 + (g2 - g1) * frac)
                b = int(b1 + (b2 - b1) * frac)
            else:
                r, g, b = hex_to_rgb(color_palette[0])

            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            uni = fixture.universe

            has_color_wheel = False
            color_wheel_channel = None
            for ch in mode.channels:
                if ch.type.lower() == 'color_wheel':
                    has_color_wheel = True
                    color_wheel_channel = ch
                    break

            has_dimmer = any(ch.type.lower() in ('dimmer', 'intensity', 'master', 'master dimmer')
                            for ch in mode.channels)

            rgb_scale = intensity_scale
            fixture_color_wheel_value = -1
            if has_color_wheel and color_wheel_channel and color_wheel_channel.color_wheel_colors:
                fixture_color_wheel_value, _ = find_closest_color_wheel_value(
                    effect.color, color_wheel_channel.color_wheel_colors)

            for i, channel in enumerate(mode.channels):
                ch_type = channel.type.lower()
                addr = fixture.address + i
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    value = int(255 * intensity_scale)
                elif ch_type == 'red':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(r * rgb_scale)
                elif ch_type == 'green':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(g * rgb_scale)
                elif ch_type == 'blue':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(b * rgb_scale)
                elif ch_type in ('white', 'cool_white', 'warm_white'):
                    value = int(min(r, g, b) * rgb_scale)
                elif ch_type == 'color_wheel':
                    if fixture_color_wheel_value >= 0:
                        value = fixture_color_wheel_value
                    else:
                        value = 0
                elif ch_type == 'shutter':
                    shutter_threshold = 0.02
                    if has_dimmer or has_color_wheel:
                        value = 255 if intensity_scale > shutter_threshold else 0
                    else:
                        if intensity_scale <= shutter_threshold:
                            value = 0
                        else:
                            value = int(51 + 204 * intensity_scale)
                elif ch_type == 'strobe':
                    value = 0
                else:
                    continue
                buffer[(uni, addr)] = (value, ch_type)

    def _buffer_chase(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """Buffer a chase effect."""
        # Apply fader level for MIDI fader control
        fader_level = getattr(self, '_fader_level', 1.0)
        master_scale = (effect.intensity / 100.0) * fader_level
        intensity_max = (effect.intensity_max if effect.intensity_max > 0 else 100) * master_scale
        intensity_min = effect.intensity_min * master_scale
        
        wave_width = 0.35
        
        # Get color palette for variety (assigns different colors to different fixtures)
        color_palette = effect.color_palette if effect.color_palette else [effect.color]
        
        for idx, fixture in enumerate(fixtures):
            fixture_pos = getattr(fixture, 'location_x', idx / max(1, len(fixtures) - 1))
            
            wave_pos = phase * (1.0 + wave_width * 2) - wave_width
            distance = abs(fixture_pos - wave_pos)
            
            if distance < wave_width:
                brightness = 1.0 - (distance / wave_width)
                fixture_intensity = intensity_min + (intensity_max - intensity_min) * brightness
            else:
                fixture_intensity = intensity_min
            
            # Select color from palette with animation - colors scroll across fixtures over time
            # This creates the color chase effect where colors move with the brightness wave
            if len(color_palette) > 1:
                color_offset = int(phase * len(fixtures))
                color_index = (idx + color_offset) % len(color_palette)
                fixture_color = color_palette[color_index]
            else:
                fixture_color = color_palette[0]
            r, g, b = hex_to_rgb(fixture_color)
            intensity_scale = fixture_intensity / 100.0
            
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = fixture.universe
            
            # Check if this fixture has a color wheel channel
            has_color_wheel = False
            color_wheel_channel = None
            for ch in mode.channels:
                if ch.type.lower() == 'color_wheel':
                    has_color_wheel = True
                    color_wheel_channel = ch
                    break
            
            # Check if fixture has a dimmer channel
            has_dimmer = any(ch.type.lower() in ('dimmer', 'intensity', 'master', 'master dimmer') 
                           for ch in mode.channels)
            
            # Apply intensity to RGB to match Timeline Editor behavior
            rgb_scale = intensity_scale
            
            # For color wheel fixtures: map color to closest wheel position
            fixture_color_wheel_value = -1
            if has_color_wheel and color_wheel_channel and color_wheel_channel.color_wheel_colors:
                fixture_color_wheel_value, matched_color_name = find_closest_color_wheel_value(
                    fixture_color, color_wheel_channel.color_wheel_colors
                )
                # Debug color wheel for spots
                if 'Spot' in fixture.label and not hasattr(self, '_color_wheel_debug'):
                    self._color_wheel_debug = {}
                if 'Spot' in fixture.label:
                    debug_key = f"{fixture.label}_{fixture_color}"
                    self._color_wheel_debug[debug_key] = self._color_wheel_debug.get(debug_key, 0) + 1
                    if self._color_wheel_debug[debug_key] % 60 == 1:
                        print(f"[ColorWheel] {fixture.label}: color={fixture_color} -> wheel_value={fixture_color_wheel_value} ({matched_color_name})")
            
            for i, channel in enumerate(mode.channels):
                ch_type = channel.type.lower()
                addr = fixture.address + i
                
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    # Chase modulates intensity per fixture
                    value = int(255 * intensity_scale)
                elif ch_type == 'red':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(r * rgb_scale)
                elif ch_type == 'green':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(g * rgb_scale)
                elif ch_type == 'blue':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(b * rgb_scale)
                elif ch_type in ('white', 'cool_white', 'warm_white'):
                    value = int(min(r, g, b) * rgb_scale)
                elif ch_type == 'color_wheel':
                    if fixture_color_wheel_value >= 0:
                        value = fixture_color_wheel_value
                    else:
                        value = 0  # Reset to open/white when using RGB
                elif ch_type == 'shutter':
                    # For chase/wave effects: close shutter when fixture is in "off" part of wave
                    # Use a threshold (2%) to avoid keeping shutter open for tiny intensities
                    shutter_threshold = 0.02  # Close shutter below 2% intensity
                    if has_dimmer or has_color_wheel:
                        # Open shutter when intensity is above threshold, close otherwise
                        value = 255 if intensity_scale > shutter_threshold else 0
                    else:
                        # For fixtures without dimmer or color wheel, use shutter for intensity
                        if intensity_scale <= shutter_threshold:
                            value = 0  # Fully closed
                        else:
                            min_shutter = 51
                            max_shutter = 255
                            value = int(min_shutter + (max_shutter - min_shutter) * intensity_scale)
                elif ch_type == 'strobe':
                    value = 0  # No strobing - let dimmer control intensity
                else:
                    continue
                
                buffer[(uni, addr)] = (value, ch_type)
    
    def _buffer_strobe(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float, start_time: float):
        """Buffer a strobe effect."""
        strobe_bpm = max(60, effect.speed_bpm) * self._global_speed_multiplier
        flashes_per_second = strobe_bpm / 60.0
        elapsed = time.time() - start_time
        strobe_phase = (elapsed * flashes_per_second) % 1.0
        
        is_on = strobe_phase < 0.5
        raw_intensity = effect.intensity_max if is_on else effect.intensity_min
        # Apply fader level for MIDI fader control
        fader_level = getattr(self, '_fader_level', 1.0)
        intensity = int(raw_intensity * (effect.intensity / 100.0) * fader_level)
        intensity_scale = intensity / 100.0
        
        # Get color palette for variety (assigns different colors to different fixtures)
        color_palette = effect.color_palette if effect.color_palette else [effect.color]
        
        for idx, fixture in enumerate(fixtures):
            # Select color from palette based on fixture index
            fixture_color = color_palette[idx % len(color_palette)]
            r, g, b = hex_to_rgb(fixture_color)
            
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = fixture.universe
            
            # Check if this fixture has a color wheel channel
            has_color_wheel = False
            color_wheel_channel = None
            for ch in mode.channels:
                if ch.type.lower() == 'color_wheel':
                    has_color_wheel = True
                    color_wheel_channel = ch
                    break
            
            # Check if fixture has a dimmer channel
            has_dimmer = any(ch.type.lower() in ('dimmer', 'intensity', 'master', 'master dimmer') 
                           for ch in mode.channels)
            
            # Apply intensity to RGB to match Timeline Editor behavior
            rgb_scale = intensity_scale
            
            # For color wheel fixtures: map color to closest wheel position
            fixture_color_wheel_value = -1
            if has_color_wheel and color_wheel_channel and color_wheel_channel.color_wheel_colors:
                fixture_color_wheel_value, matched_color_name = find_closest_color_wheel_value(
                    fixture_color, color_wheel_channel.color_wheel_colors
                )
            
            for i, channel in enumerate(mode.channels):
                ch_type = channel.type.lower()
                addr = fixture.address + i
                
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    # Strobe modulates intensity on/off
                    value = int(255 * intensity_scale)
                elif ch_type == 'red':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(r * rgb_scale)
                elif ch_type == 'green':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(g * rgb_scale)
                elif ch_type == 'blue':
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        continue
                    value = int(b * rgb_scale)
                elif ch_type in ('white', 'cool_white', 'warm_white'):
                    value = int(min(r, g, b) * rgb_scale)
                elif ch_type == 'color_wheel':
                    if fixture_color_wheel_value >= 0:
                        value = fixture_color_wheel_value
                    else:
                        value = 0  # Reset to open/white when using RGB
                elif ch_type == 'shutter':
                    value = 255 if is_on else 0
                elif ch_type == 'strobe':
                    # Strobe-only channels: on/off with intensity scaling
                    value = int(255 * intensity_scale) if is_on else 0
                else:
                    continue
                
                buffer[(uni, addr)] = (value, ch_type)
    
    # ── Dimmer effect buffer methods ─────────────────────────────────────
    def _buffer_dimmer_effect(self, buffer: dict, fixtures: list, effect: EffectParameters,
                              phase: float, start_time: float):
        """Buffer a dimmer-layer effect.  Only writes dimmer/shutter channels.

        The ``dimmer_effect`` field on *effect* selects which spatial/temporal
        pattern to use.  All modes respect intensity, intensity_min/max, speed,
        and direction.
        """
        dimmer_mode = getattr(effect, 'dimmer_effect', 'on') or 'on'

        # Pre-compute common values
        fader_level = getattr(self, '_fader_level', 1.0)
        master = (effect.intensity / 100.0) * fader_level
        i_min = effect.intensity_min * master / 100.0  # 0-1
        i_max = (effect.intensity_max if effect.intensity_max > 0 else 100) * master / 100.0

        # Build per-fixture brightness list  (one float 0-1 per fixture)
        n = max(len(fixtures), 1)
        brightnesses = [0.0] * n

        if dimmer_mode == 'on':
            # All fixtures at max intensity, no animation
            brightnesses = [i_max] * n

        elif dimmer_mode == 'fade':
            # Simple sine fade, all fixtures in sync
            v = 0.5 + 0.5 * math.sin(phase * 2 * math.pi)
            brightnesses = [i_min + (i_max - i_min) * v] * n

        elif dimmer_mode == 'random_fade':
            # Each fixture gets its own pseudo-random phase offset
            for idx in range(n):
                seed_offset = ((idx * 71 + 37) % 100) / 100.0
                fp = (phase + seed_offset) % 1.0
                v = 0.5 + 0.5 * math.sin(fp * 2 * math.pi)
                brightnesses[idx] = i_min + (i_max - i_min) * v

        elif dimmer_mode == 'odd_even':
            # Odd fixtures up when even are down and vice-versa
            v = 0.5 + 0.5 * math.sin(phase * 2 * math.pi)
            for idx in range(n):
                if idx % 2 == 0:
                    brightnesses[idx] = i_min + (i_max - i_min) * v
                else:
                    brightnesses[idx] = i_min + (i_max - i_min) * (1.0 - v)

        elif dimmer_mode in ('left_right', 'right_left'):
            wave_width = max(0.05, effect.fixture_offset)
            for idx, fx in enumerate(fixtures):
                pos = getattr(fx, 'location_x', idx / max(1, n - 1))
                if dimmer_mode == 'right_left':
                    pos = 1.0 - pos
                wave_pos = phase * (1.0 + wave_width * 2) - wave_width
                dist = abs(pos - wave_pos)
                if dist < wave_width:
                    v = 1.0 - (dist / wave_width)
                    brightnesses[idx] = i_min + (i_max - i_min) * v
                else:
                    brightnesses[idx] = i_min

        elif dimmer_mode in ('top_down', 'bottom_up'):
            wave_width = max(0.05, effect.fixture_offset)
            for idx, fx in enumerate(fixtures):
                pos = getattr(fx, 'location_y', idx / max(1, n - 1))
                if dimmer_mode == 'bottom_up':
                    pos = 1.0 - pos
                wave_pos = phase * (1.0 + wave_width * 2) - wave_width
                dist = abs(pos - wave_pos)
                if dist < wave_width:
                    v = 1.0 - (dist / wave_width)
                    brightnesses[idx] = i_min + (i_max - i_min) * v
                else:
                    brightnesses[idx] = i_min

        elif dimmer_mode == 'center_out':
            wave_width = max(0.05, effect.fixture_offset)
            for idx, fx in enumerate(fixtures):
                cx = getattr(fx, 'location_x', idx / max(1, n - 1))
                cy = getattr(fx, 'location_y', 0.5)
                dist_from_center = math.sqrt((cx - 0.5) ** 2 + (cy - 0.5) ** 2) / 0.7071
                ring_pos = phase * (1.0 + wave_width * 2) - wave_width
                dist = abs(dist_from_center - ring_pos)
                if dist < wave_width:
                    v = 1.0 - (dist / wave_width)
                    brightnesses[idx] = i_min + (i_max - i_min) * v
                else:
                    brightnesses[idx] = i_min

        elif dimmer_mode == 'edges_in':
            wave_width = max(0.05, effect.fixture_offset)
            for idx, fx in enumerate(fixtures):
                cx = getattr(fx, 'location_x', idx / max(1, n - 1))
                cy = getattr(fx, 'location_y', 0.5)
                dist_from_center = math.sqrt((cx - 0.5) ** 2 + (cy - 0.5) ** 2) / 0.7071
                ring_pos = (1.0 - phase) * (1.0 + wave_width * 2) - wave_width
                dist = abs(dist_from_center - ring_pos)
                if dist < wave_width:
                    v = 1.0 - (dist / wave_width)
                    brightnesses[idx] = i_min + (i_max - i_min) * v
                else:
                    brightnesses[idx] = i_min

        elif dimmer_mode == 'sparkle':
            # Random twinkle — ~20% of fixtures lit at any moment, smooth transitions
            frame = int(phase * 200) % 200
            for idx in range(n):
                seed = (idx * 7 + frame * 13) % 100
                if seed < 20:
                    v = 0.5 + (seed % 50) / 100.0
                    brightnesses[idx] = i_min + (i_max - i_min) * v
                else:
                    brightnesses[idx] = i_min

        elif dimmer_mode == 'strobe_fade':
            # Quick flash on, slow exponential decay
            decay_phase = phase % 1.0
            v = math.exp(-decay_phase * 5.0)  # fast decay
            brightnesses = [i_min + (i_max - i_min) * v] * n

        elif dimmer_mode == 'build_up':
            # Fixtures sequentially turn on and stay on
            lit_count = int(phase * (n + 1))
            for idx in range(n):
                # Sort by location_x for spatial ordering
                brightnesses[idx] = i_max if idx < lit_count else i_min

        elif dimmer_mode == 'knockdown':
            # Fixtures sequentially turn off
            off_count = int(phase * (n + 1))
            for idx in range(n):
                brightnesses[idx] = i_min if idx < off_count else i_max

        elif dimmer_mode == 'wave':
            # Travelling sine wave across fixtures.  The spatial term spreads
            # the rig along the wave while the temporal term (phase) scrolls
            # it, so the wave always animates — even when every fixture shares
            # the same physical location.  Blending in the fixture index keeps
            # co-located fixtures from pulsing in unison.
            for idx, fx in enumerate(fixtures):
                pos = getattr(fx, 'location_x', None)
                if pos is None:
                    pos = idx / max(1, n - 1)
                spatial = pos + (idx / max(1, n)) * 0.5
                wave_val = 0.5 + 0.5 * math.sin(spatial * 2 * math.pi * 1.5 - phase * 2 * math.pi)
                brightnesses[idx] = i_min + (i_max - i_min) * wave_val

        elif dimmer_mode == 'checkerboard':
            # Alternating groups flip-flop based on 2D position
            v = 0.5 + 0.5 * math.sin(phase * 2 * math.pi)
            for idx, fx in enumerate(fixtures):
                cx = getattr(fx, 'location_x', (idx % 4) / 4.0)
                cy = getattr(fx, 'location_y', 0.5)
                cell = (int(cx * 4) + int(cy * 4)) % 2
                if cell == 0:
                    brightnesses[idx] = i_min + (i_max - i_min) * v
                else:
                    brightnesses[idx] = i_min + (i_max - i_min) * (1.0 - v)

        elif dimmer_mode == 'breathe':
            # Organic breathing — similar to fade but with steeper ramp
            t = phase * 2 * math.pi
            v = (math.exp(math.sin(t)) - 0.3679) / (2.3504 - 0.3679)
            brightnesses = [i_min + (i_max - i_min) * v] * n

        elif dimmer_mode == 'lightning':
            # Random flickers of full intensity with dark gaps
            elapsed = time.time() - start_time
            # Use fast modular hash for pseudo-random flicker
            tick = int(elapsed * 30)  # 30 ticks/sec
            flash = ((tick * 997) % 127) < 20  # ~16% flash probability
            v = i_max if flash else i_min
            # Vary per fixture slightly
            for idx in range(n):
                fx_flash = ((tick * 997 + idx * 53) % 127) < 18
                brightnesses[idx] = i_max if fx_flash else i_min

        else:
            # Fallback — simple static dimmer at master level
            brightnesses = [i_max] * n

        # Write dimmer/shutter channels only for each fixture.
        # Dimmer layers must NOT touch RGB/color channels; they control
        # brightness exclusively via dimmer/intensity/master/shutter so
        # they don't override colors set by other layers.

        # ── Pixel-mapped fixtures ─────────────────────────────────────────
        # Separate pixel fixtures from regular fixtures so we can handle
        # per-pixel brightness for LED bars, strips, etc.
        pixel_fixtures = [f for f in fixtures if getattr(f.profile, 'is_pixel_fixture', False)
                          and getattr(f.profile, 'pixel_channel_table', None)]

        # --- Handle pixel-mapped fixtures (master dimmer only) ---
        # Dimmer layers only set master dimmers for pixel fixtures — they
        # must NOT write per-pixel RGB (that would turn them white).
        if pixel_fixtures:
            try:
                fixture_max_intensity = {}
                for idx, fx in enumerate(fixtures):
                    if id(fx) in {id(pf) for pf in pixel_fixtures}:
                        bri = max(0.0, min(1.0, brightnesses[idx]))
                        fixture_max_intensity[fx.id] = int(255 * bri)
                set_pixel_fixture_master_dimmers(
                    buffer, pixel_fixtures,
                    intensity_per_fixture=fixture_max_intensity)
            except Exception as e:
                print(f"[Dimmer] ERROR in pixel path: {e}", flush=True)
                import traceback
                traceback.print_exc()

        # --- Handle ALL fixtures at fixture level (master dimmer, shutter, RGB) ---
        # This includes pixel fixtures so their fixture-level master dimmer/shutter
        # is always set, enabling whole-fixture on/off and flashing effects.
        is_pixel = set(id(f) for f in pixel_fixtures)
        for idx, fixture in enumerate(fixtures):
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            uni = fixture.universe
            bri = max(0.0, min(1.0, brightnesses[idx]))

            # For pixel fixtures, ALL channels are already handled above by the
            # pixel path (per-pixel RGB) + set_pixel_fixture_master_dimmers
            # (master dimmer, shutter, strobe, on_off).  Writing them again
            # here with a per-fixture brightness would overwrite the correct
            # per-pixel-max value and cause flicker.
            if id(fixture) in is_pixel:
                continue

            has_dimmer = any(ch.type.lower() in ('dimmer', 'intensity', 'master', 'master dimmer')
                            for ch in mode.channels)

            for i, channel in enumerate(mode.channels):
                ch_type = channel.type.lower()
                addr = fixture.address + i

                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    buffer[(uni, addr)] = (int(255 * bri), ch_type)
                elif ch_type == 'shutter':
                    shutter_override = getattr(effect, 'shutter_value', -1)
                    if shutter_override >= 0:
                        buffer[(uni, addr)] = (shutter_override, ch_type)
                    elif has_dimmer:
                        buffer[(uni, addr)] = (255 if bri > 0.02 else 0, ch_type)
                    else:
                        if bri <= 0.02:
                            buffer[(uni, addr)] = (0, ch_type)
                        else:
                            buffer[(uni, addr)] = (int(51 + (255 - 51) * bri), ch_type)
                elif ch_type == 'strobe':
                    buffer[(uni, addr)] = (0, ch_type)

    def _dimmer_brightness_at(self, dimmer_mode: str, phase: float,
                              nx: float, ny: float, idx: int, n: int,
                              i_min: float, i_max: float,
                              effect, start_time: float) -> float:
        """Return brightness (0-1) for a single point given dimmer mode and normalised position.

        Used by both per-fixture and per-pixel paths so the pattern look is identical
        regardless of fixture type.
        """
        if dimmer_mode == 'fade':
            v = 0.5 + 0.5 * math.sin(phase * 2 * math.pi)
            return i_min + (i_max - i_min) * v

        elif dimmer_mode == 'random_fade':
            seed_offset = ((idx * 71 + 37) % 100) / 100.0
            fp = (phase + seed_offset) % 1.0
            v = 0.5 + 0.5 * math.sin(fp * 2 * math.pi)
            return i_min + (i_max - i_min) * v

        elif dimmer_mode == 'odd_even':
            v = 0.5 + 0.5 * math.sin(phase * 2 * math.pi)
            if idx % 2 == 0:
                return i_min + (i_max - i_min) * v
            else:
                return i_min + (i_max - i_min) * (1.0 - v)

        elif dimmer_mode in ('left_right', 'right_left'):
            wave_width = max(0.05, effect.fixture_offset)
            pos = 1.0 - nx if dimmer_mode == 'right_left' else nx
            wave_pos = phase * (1.0 + wave_width * 2) - wave_width
            dist = abs(pos - wave_pos)
            if dist < wave_width:
                v = 1.0 - (dist / wave_width)
                return i_min + (i_max - i_min) * v
            return i_min

        elif dimmer_mode in ('top_down', 'bottom_up'):
            wave_width = max(0.05, effect.fixture_offset)
            pos = 1.0 - ny if dimmer_mode == 'bottom_up' else ny
            wave_pos = phase * (1.0 + wave_width * 2) - wave_width
            dist = abs(pos - wave_pos)
            if dist < wave_width:
                v = 1.0 - (dist / wave_width)
                return i_min + (i_max - i_min) * v
            return i_min

        elif dimmer_mode == 'center_out':
            wave_width = max(0.05, effect.fixture_offset)
            dist_from_center = math.sqrt((nx - 0.5) ** 2 + (ny - 0.5) ** 2) / 0.7071
            ring_pos = phase * (1.0 + wave_width * 2) - wave_width
            dist = abs(dist_from_center - ring_pos)
            if dist < wave_width:
                v = 1.0 - (dist / wave_width)
                return i_min + (i_max - i_min) * v
            return i_min

        elif dimmer_mode == 'edges_in':
            wave_width = max(0.05, effect.fixture_offset)
            dist_from_center = math.sqrt((nx - 0.5) ** 2 + (ny - 0.5) ** 2) / 0.7071
            ring_pos = (1.0 - phase) * (1.0 + wave_width * 2) - wave_width
            dist = abs(dist_from_center - ring_pos)
            if dist < wave_width:
                v = 1.0 - (dist / wave_width)
                return i_min + (i_max - i_min) * v
            return i_min

        elif dimmer_mode == 'sparkle':
            frame = int(phase * 200) % 200
            seed = (idx * 7 + frame * 13) % 100
            if seed < 20:
                v = 0.5 + (seed % 50) / 100.0
                return i_min + (i_max - i_min) * v
            return i_min

        elif dimmer_mode == 'strobe_fade':
            v = math.exp(-(phase % 1.0) * 5.0)
            return i_min + (i_max - i_min) * v

        elif dimmer_mode == 'build_up':
            lit_frac = phase
            pos = nx  # spatial order left-to-right
            return i_max if pos <= lit_frac else i_min

        elif dimmer_mode == 'knockdown':
            off_frac = phase
            pos = nx
            return i_min if pos <= off_frac else i_max

        elif dimmer_mode == 'wave':
            # Decouple temporal scroll from spatial frequency so the wave keeps
            # moving even when fixtures share a position (see per-fixture path).
            spatial = nx + (idx / max(1, n)) * 0.5
            wave_val = 0.5 + 0.5 * math.sin(spatial * 2 * math.pi * 1.5 - phase * 2 * math.pi)
            return i_min + (i_max - i_min) * wave_val

        elif dimmer_mode == 'checkerboard':
            v = 0.5 + 0.5 * math.sin(phase * 2 * math.pi)
            cell = (int(nx * 4) + int(ny * 4)) % 2
            if cell == 0:
                return i_min + (i_max - i_min) * v
            return i_min + (i_max - i_min) * (1.0 - v)

        elif dimmer_mode == 'breathe':
            t = phase * 2 * math.pi
            v = (math.exp(math.sin(t)) - 0.3679) / (2.3504 - 0.3679)
            return i_min + (i_max - i_min) * v

        elif dimmer_mode == 'lightning':
            elapsed = time.time() - start_time
            tick = int(elapsed * 30)
            fx_flash = ((tick * 997 + idx * 53) % 127) < 18
            return i_max if fx_flash else i_min

        # fallback
        return i_max

    def _buffer_rainbow(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """Buffer a rainbow effect."""
        # Apply fader level for MIDI fader control
        fader_level = getattr(self, '_fader_level', 1.0)
        intensity_scale = (effect.intensity / 100.0) * fader_level
        
        for idx, fixture in enumerate(fixtures):
            # Offset phase per fixture for rainbow spread
            fixture_phase = (phase + idx * 0.1) % 1.0
            color = get_rainbow_color(fixture_phase)
            r, g, b = hex_to_rgb(color)
            
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = fixture.universe
            
            # Check if this fixture has a color wheel channel
            has_color_wheel = False
            color_wheel_channel = None
            for ch in mode.channels:
                if ch.type.lower() == 'color_wheel':
                    has_color_wheel = True
                    color_wheel_channel = ch
                    break
            
            # Check if fixture has a dimmer channel
            has_dimmer = any(ch.type.lower() in ('dimmer', 'intensity', 'master', 'master dimmer') 
                           for ch in mode.channels)
            
            # Apply intensity to RGB to match Timeline Editor behavior
            rgb_scale = intensity_scale
            
            # For color wheel fixtures: map rainbow color to closest wheel position
            fixture_color_wheel_value = -1
            if has_color_wheel and color_wheel_channel and color_wheel_channel.color_wheel_colors:
                fixture_color_wheel_value, matched_color_name = find_closest_color_wheel_value(
                    color, color_wheel_channel.color_wheel_colors
                )
            
            for i, channel in enumerate(mode.channels):
                ch_type = channel.type.lower()
                addr = fixture.address + i
                
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    value = 255  # Full value - merge loop will scale by fader
                elif ch_type == 'red':
                    # Set RGB to 0 if using color wheel to prevent color mixing
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        value = 0  # Clear RGB when using color wheel
                    else:
                        value = int(r * rgb_scale)
                elif ch_type == 'green':
                    # Set RGB to 0 if using color wheel to prevent color mixing
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        value = 0  # Clear RGB when using color wheel
                    else:
                        value = int(g * rgb_scale)
                elif ch_type == 'blue':
                    # Set RGB to 0 if using color wheel to prevent color mixing
                    if has_color_wheel and fixture_color_wheel_value >= 0:
                        value = 0  # Clear RGB when using color wheel
                    else:
                        value = int(b * rgb_scale)
                elif ch_type in ('white', 'cool_white', 'warm_white'):
                    value = int(min(r, g, b) * rgb_scale)
                elif ch_type == 'color_wheel':
                    # Set color wheel to the mapped rainbow color
                    if fixture_color_wheel_value >= 0:
                        value = fixture_color_wheel_value
                    else:
                        continue  # Skip - no color wheel value
                elif ch_type == 'shutter':
                    value = 255  # Open shutter
                elif ch_type == 'strobe':
                    value = 0  # No strobing - let dimmer control intensity
                else:
                    continue
                
                buffer[(uni, addr)] = (value, ch_type)

    # =========================================================================
    # Pixel-Mapped Effect Methods
    # =========================================================================

    def _buffer_pixel_chase(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """
        Buffer a pixel chase effect - a wave of light that moves across all pixels.
        
        Pixels are sorted by their canvas X position so the chase moves left-to-right
        across the stage regardless of how fixtures are arranged or addressed.
        """
        # Apply fader level for MIDI fader control
        fader_level = getattr(self, '_fader_level', 1.0)
        master_scale = (effect.intensity / 100.0) * fader_level
        intensity_max = (effect.intensity_max if effect.intensity_max > 0 else 100) * master_scale
        intensity_min = effect.intensity_min * master_scale
        
        # Width of the chase wave (0.0 to 1.0 of the total spread)
        wave_width = 0.25
        
        # Get color palette
        color_palette = effect.color_palette if effect.color_palette else [effect.color]
        
        # Get all pixels sorted by canvas position
        all_pixels = get_all_pixel_positions(fixtures)
        
        # Debug: Check for pixel fixtures (show once per app session)
        if not hasattr(self, '_pixel_chase_debug_shown'):
            self._pixel_chase_debug_shown = True
            pixel_fixtures = [f for f in fixtures if f.profile.is_pixel_fixture]
            print(f"[PixelChase] Total fixtures: {len(fixtures)}, Pixel fixtures: {len(pixel_fixtures)}")
            for f in pixel_fixtures:
                print(f"  - {f.label}: is_pixel={f.profile.is_pixel_fixture}, "
                      f"pixel_table={len(f.profile.pixel_channel_table) if f.profile.pixel_channel_table else 0} entries")
            print(f"[PixelChase] Total pixels found: {len(all_pixels)}")
        
        if not all_pixels:
            # Fall back to regular chase for non-pixel fixtures
            self._buffer_chase(buffer, fixtures, effect, phase)
            return
        
        # Get the X range of all pixels
        min_x = min(p['canvas_x'] for p in all_pixels)
        max_x = max(p['canvas_x'] for p in all_pixels)
        x_range = max(max_x - min_x, 0.001)  # Prevent division by zero
        
        # Apply direction
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        # Track max intensity per fixture for master dimmer setting
        fixture_max_intensity: dict[str, float] = {}
        
        for idx, pixel in enumerate(all_pixels):
            # Handle random direction
            if effect.direction == 'random':
                import random
                random.seed(int(phase * 1000) // 100 + idx + pixel.get('pixel_num', 0))
                # Random: on/off at max/min intensity
                pixel_intensity = intensity_max if random.random() > 0.5 else intensity_min
            else:
                # Normal wave chase
                # Normalize pixel position to 0.0-1.0 range
                norm_pos = (pixel['canvas_x'] - min_x) / x_range
                
                # Calculate wave position (extends beyond 0-1 to allow wave to exit)
                wave_pos = phase * (1.0 + wave_width * 2) - wave_width
                distance = abs(norm_pos - wave_pos)
                
                # Calculate brightness based on distance from wave center
                if distance < wave_width:
                    brightness = 1.0 - (distance / wave_width)
                    pixel_intensity = intensity_min + (intensity_max - intensity_min) * brightness
                else:
                    pixel_intensity = intensity_min
            
            intensity_scale = pixel_intensity / 100.0
            
            # Track max intensity for this pixel's fixture
            fixture = pixel.get('fixture')
            if fixture:
                fixture_id = fixture.id
                current_max = fixture_max_intensity.get(fixture_id, 0.0)
                fixture_max_intensity[fixture_id] = max(current_max, intensity_scale)
            
            # Select color from palette - colors scroll with the wave
            if len(color_palette) > 1:
                color_offset = int(phase * len(all_pixels))
                color_index = (idx + color_offset) % len(color_palette)
                pixel_color = color_palette[color_index]
            else:
                pixel_color = color_palette[0]
            
            r, g, b = hex_to_rgb(pixel_color)
            apply_color_to_pixel(buffer, pixel, r, g, b, intensity_scale)
        
        # Set fixture master dimmers based on max pixel intensity
        # This ensures fixtures go fully dark when all their pixels are off
        intensity_per_fixture = {fid: int(255 * scale) for fid, scale in fixture_max_intensity.items()}
        set_pixel_fixture_master_dimmers(buffer, fixtures, intensity_per_fixture)

    def _buffer_pixel_rainbow(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """
        Buffer a pixel rainbow effect - rainbow colors spread across all pixels.
        
        Colors are assigned based on canvas position so the rainbow appears
        visually correct on stage regardless of fixture/pixel addressing.
        """
        print(f"[_buffer_pixel_rainbow] CALLED with {len(fixtures)} fixtures", flush=True)
        # Apply fader level for MIDI fader control
        fader_level = getattr(self, '_fader_level', 1.0)
        intensity_scale = (effect.intensity / 100.0) * fader_level
        
        # Get all pixels sorted by canvas position
        all_pixels = get_all_pixel_positions(fixtures)
        
        # Debug pixel fixture detection (always print first time)
        if not hasattr(self, '_pixel_rainbow_debug_shown'):
            self._pixel_rainbow_debug_shown = True
            import sys
            print(f"[PixelRainbow] Total fixtures: {len(fixtures)}, Pixels found: {len(all_pixels)}", flush=True)
            for f in fixtures:
                is_pixel = getattr(f.profile, 'is_pixel_fixture', False)
                pct = f.profile.pixel_channel_table if hasattr(f.profile, 'pixel_channel_table') else None
                pct_len = len(pct) if pct else 0
                if is_pixel or pct_len > 0:
                    print(f"  [PixelRainbow] {f.label}: is_pixel={is_pixel}, pixel_table_entries={pct_len}", flush=True)
            sys.stdout.flush()
        
        if not all_pixels:
            # Fall back to regular rainbow for non-pixel fixtures
            self._buffer_rainbow(buffer, fixtures, effect, phase)
            return
        
        # Get the X range of all pixels for horizontal rainbow
        min_x = min(p['canvas_x'] for p in all_pixels)
        max_x = max(p['canvas_x'] for p in all_pixels)
        x_range = max(max_x - min_x, 0.001)
        
        # Track max intensity per fixture for master dimmer setting
        fixture_max_intensity: dict[str, float] = {}
        
        for pixel in all_pixels:
            # Normalize pixel position
            norm_pos = (pixel['canvas_x'] - min_x) / x_range
            
            # Calculate hue based on position + animation phase
            hue = (norm_pos + phase) % 1.0
            color = get_rainbow_color(hue)
            r, g, b = hex_to_rgb(color)
            
            # Track max intensity for this pixel's fixture
            fixture = pixel.get('fixture')
            if fixture:
                fixture_id = fixture.id
                current_max = fixture_max_intensity.get(fixture_id, 0.0)
                fixture_max_intensity[fixture_id] = max(current_max, intensity_scale)
            
            apply_color_to_pixel(buffer, pixel, r, g, b, intensity_scale)
        
        # Set fixture master dimmers based on max pixel intensity
        intensity_per_fixture = {fid: int(255 * scale) for fid, scale in fixture_max_intensity.items()}
        set_pixel_fixture_master_dimmers(buffer, fixtures, intensity_per_fixture)

    def _buffer_pixel_wipe(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """
        Buffer a pixel wipe effect - a solid color wipe that reveals/hides pixels.
        
        The wipe moves across the canvas, turning pixels on or off based on position.
        """
        # Apply fader level for MIDI fader control
        fader_level = getattr(self, '_fader_level', 1.0)
        intensity_scale = (effect.intensity / 100.0) * fader_level
        
        # Get color
        color = effect.color
        r, g, b = hex_to_rgb(color)
        
        # Get all pixels sorted by canvas position
        all_pixels = get_all_pixel_positions(fixtures)
        if not all_pixels:
            # Fall back to static for non-pixel fixtures
            self._buffer_static(buffer, fixtures, effect)
            return
        
        # Get the X range of all pixels
        min_x = min(p['canvas_x'] for p in all_pixels)
        max_x = max(p['canvas_x'] for p in all_pixels)
        x_range = max(max_x - min_x, 0.001)
        
        # Apply direction
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        # Wipe position (0.0 to 1.0)
        wipe_pos = phase
        
        # Softness of the wipe edge (0 = hard edge, higher = softer)
        edge_softness = 0.05
        
        # Track max intensity per fixture for master dimmer setting
        fixture_max_intensity: dict[str, float] = {}
        
        for pixel in all_pixels:
            # Normalize pixel position
            norm_pos = (pixel['canvas_x'] - min_x) / x_range
            
            # Calculate pixel brightness based on wipe position
            if norm_pos < wipe_pos - edge_softness:
                # Fully on (wipe has passed)
                pixel_intensity = 1.0
            elif norm_pos > wipe_pos + edge_softness:
                # Fully off (wipe hasn't reached)
                pixel_intensity = 0.0
            else:
                # In the edge region - fade
                fade_pos = (wipe_pos + edge_softness - norm_pos) / (edge_softness * 2)
                pixel_intensity = max(0.0, min(1.0, fade_pos))
            
            final_intensity = intensity_scale * pixel_intensity
            
            # Track max intensity for this pixel's fixture
            fixture = pixel.get('fixture')
            if fixture:
                fixture_id = fixture.id
                current_max = fixture_max_intensity.get(fixture_id, 0.0)
                fixture_max_intensity[fixture_id] = max(current_max, final_intensity)
                # Ensure strobe fixtures go fully dark when pixel_intensity is 0
                mode = fixture.profile.get_mode(fixture.mode_name)
                mode_channels = mode.channels if mode else []
                base_addr = fixture.address
                uni = fixture.universe
                if pixel_intensity == 0.0:
                    for i, ch in enumerate(mode_channels):
                        ch_type = ch.type.lower()
                        addr = base_addr + i
                        if ch_type in ('strobe', 'dimmer', 'intensity', 'master', 'master dimmer'):
                            buffer[(uni, addr)] = (0, ch_type)
            
            apply_color_to_pixel(buffer, pixel, r, g, b, final_intensity)
        
        # Set fixture master dimmers based on max pixel intensity
        intensity_per_fixture = {fid: int(255 * scale) for fid, scale in fixture_max_intensity.items()}
        set_pixel_fixture_master_dimmers(buffer, fixtures, intensity_per_fixture)

    # ── Generic geo-effect → buffer adapter ──────────────────────────────
    def _buffer_geo_adapter(self, buffer: dict, fixtures: list, effect: EffectParameters,
                            phase: float, geo_method_name: str):
        """Run any _apply_geo_* method through the HTP buffer.

        Uses thread-local storage so that ``_apply_color_to_pixel`` redirects
        its Art-Net writes into *buffer* for the duration of the geo method call.
        This is thread-safe — each HTP effect thread has its own TLS slot.
        """
        import threading
        if not hasattr(self, '_buffer_capture_tls'):
            self._buffer_capture_tls = threading.local()
        tls = self._buffer_capture_tls
        tls.buffer = buffer
        tls.fixture_max_intensity = {}
        tls.active = True
        try:
            method = getattr(self, geo_method_name, None)
            if method is None:
                print(f"[HTP] WARNING: geo method '{geo_method_name}' not found")
                self._buffer_static(buffer, fixtures, effect)
                return
            method(fixtures, effect, phase)
        except Exception as e:
            print(f"[HTP] ERROR in geo adapter ({geo_method_name}): {e}", flush=True)
            import traceback
            traceback.print_exc()
            # Fall back to static so the effect still produces visible output
            self._buffer_static(buffer, fixtures, effect)
        finally:
            tls.active = False
        # Set master dimmers from tracked intensities
        fmi = tls.fixture_max_intensity
        intensity_per_fixture = {fid: int(255 * s) for fid, s in fmi.items()}
        set_pixel_fixture_master_dimmers(buffer, fixtures, intensity_per_fixture)

    def _buffer_ensemble_adapter(self, buffer: dict, fixtures: list, effect: EffectParameters,
                                 phase: float, method_name: str):
        """Run any _apply_ensemble_* method through the HTP buffer.

        Ensemble handlers paint pixels via ``_apply_color_to_pixel`` (already
        buffer-aware) and movers/wash via ``_apply_mover_position`` /
        ``apply_static``.  With the thread-local capture flag set, all three
        redirect their writes into *buffer* so the HTP merge loop can blend the
        animated ensemble output instead of rendering it as a static colour.
        This is what makes ensembles animate in the song-timeline preview /
        playback the same way they do when triggered from the preset panel.
        """
        import threading
        if not hasattr(self, '_buffer_capture_tls'):
            self._buffer_capture_tls = threading.local()
        tls = self._buffer_capture_tls
        tls.buffer = buffer
        tls.fixture_max_intensity = {}
        tls.active = True
        try:
            method = getattr(self, method_name, None)
            if method is None:
                print(f"[HTP] WARNING: ensemble method '{method_name}' not found")
                self._buffer_static(buffer, fixtures, effect)
                return
            method(fixtures, effect, phase)
        except Exception as e:
            print(f"[HTP] ERROR in ensemble adapter ({method_name}): {e}", flush=True)
            import traceback
            traceback.print_exc()
            # Fall back to static so the effect still produces visible output
            self._buffer_static(buffer, fixtures, effect)
        finally:
            tls.active = False
        # Set master dimmers from tracked pixel intensities.  Movers/wash write
        # their own dimmer channels directly into the buffer, so only pixel
        # fixtures (tracked in fmi) need a master-dimmer pass.
        fmi = tls.fixture_max_intensity
        if fmi:
            intensity_per_fixture = {fid: int(255 * s) for fid, s in fmi.items()}
            set_pixel_fixture_master_dimmers(buffer, fixtures, intensity_per_fixture)

    def _buffer_pixel_snake(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """Buffer a glowing snake that slithers across the pixel canvas.
        
        The snake head follows a Lissajous curve and leaves a fading tail.
        Converted from _apply_pixel_snake for HTP buffer output.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._buffer_static(buffer, fixtures, effect)
            return

        fader_level = getattr(self, '_fader_level', 1.0)
        intensity_scale = (effect.intensity / 100.0) * fader_level
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']

        num_segments = 20
        snake_width = max(metrics['pixel_radius'], 0.12)

        segments = []
        for seg in range(num_segments):
            t = phase - seg * 0.012
            seg_x = 0.5 + 0.4 * math.sin(t * 2 * math.pi * 1.3)
            seg_y = 0.5 + 0.4 * math.cos(t * 2 * math.pi * 0.7)
            segments.append((seg_x, seg_y, 1.0 - seg / num_segments))

        r_base, g_base, b_base = hex_to_rgb(effect.color)
        fixture_max_intensity: dict[str, float] = {}

        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            best_brightness = 0.0
            best_seg_idx = -1

            for seg_idx, (seg_x, seg_y, falloff) in enumerate(segments):
                dx = (nx - seg_x) * sx
                dy = (ny - seg_y) * sy
                dist = (dx * dx + dy * dy) ** 0.5
                if dist < snake_width:
                    b_val = (1.0 - dist / snake_width) * falloff
                    if b_val > best_brightness:
                        best_brightness = b_val
                        best_seg_idx = seg_idx

            if best_brightness > 0:
                if best_seg_idx == 0:
                    r, g, b = 255, 255, 255
                elif best_seg_idx < 3:
                    r, g, b = r_base, g_base, b_base
                else:
                    fade = best_seg_idx / num_segments
                    r = int(r_base * (1.0 - fade * 0.6))
                    g = int(g_base * (1.0 - fade * 0.6))
                    b = int(b_base * (1.0 - fade * 0.6))
                px_scale = best_brightness * intensity_scale
            else:
                r, g, b = 0, 0, 0
                px_scale = 0.0

            fixture = pixel.get('fixture')
            if fixture:
                fixture_max_intensity[fixture.id] = max(
                    fixture_max_intensity.get(fixture.id, 0.0), px_scale)
            apply_color_to_pixel(buffer, pixel, r, g, b, px_scale)

        intensity_per_fixture = {fid: int(255 * s) for fid, s in fixture_max_intensity.items()}
        set_pixel_fixture_master_dimmers(buffer, fixtures, intensity_per_fixture)

    def _buffer_pixel_rain_drops(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """Buffer rain drops falling with expanding ripples on the pixel canvas.
        
        Converted from _apply_pixel_rain_drops for HTP buffer output.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._buffer_static(buffer, fixtures, effect)
            return

        fader_level = getattr(self, '_fader_level', 1.0)
        intensity_scale = (effect.intensity / 100.0) * fader_level
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']
        pr = metrics['pixel_radius']
        r_base, g_base, b_base = hex_to_rgb(effect.color)

        num_drops = 5
        drop_width = max(pr, 0.06)
        ring_width = max(pr * 0.8, 0.05)
        fixture_max_intensity: dict[str, float] = {}

        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            total_brightness = 0.0

            for d in range(num_drops):
                drop_phase = (phase * 1.5 + d * 0.2) % 1.0
                drop_x = (0.15 + d * 0.18) % 1.0

                if drop_phase < 0.5:
                    drop_y = drop_phase * 2.0
                    dx = (nx - drop_x) * sx
                    dy = (ny - drop_y) * sy
                    dist = (dx * dx + dy * dy) ** 0.5
                    if dist < drop_width:
                        total_brightness += (1.0 - dist / drop_width)
                else:
                    ripple_age = (drop_phase - 0.5) * 2.0
                    ripple_radius = ripple_age * 0.4
                    dx = (nx - drop_x) * sx
                    dy = (ny - 1.0) * sy
                    dist = (dx * dx + dy * dy) ** 0.5
                    ring_dist = abs(dist - ripple_radius)
                    if ring_dist < ring_width:
                        ring_brightness = (1.0 - ring_dist / ring_width) * (1.0 - ripple_age)
                        total_brightness += ring_brightness

            total_brightness = min(1.0, total_brightness)
            if total_brightness > 0.01:
                r = min(255, int(r_base * 0.5 + 100 * total_brightness))
                g = min(255, int(g_base * 0.5 + 130 * total_brightness))
                b = min(255, int(b_base * 0.5 + 200 * total_brightness))
                px_scale = total_brightness * intensity_scale
            else:
                r, g, b = 0, 0, 0
                px_scale = 0.0

            fixture = pixel.get('fixture')
            if fixture:
                fixture_max_intensity[fixture.id] = max(
                    fixture_max_intensity.get(fixture.id, 0.0), px_scale)
            apply_color_to_pixel(buffer, pixel, r, g, b, px_scale)

        intensity_per_fixture = {fid: int(255 * s) for fid, s in fixture_max_intensity.items()}
        set_pixel_fixture_master_dimmers(buffer, fixtures, intensity_per_fixture)

    def _buffer_pixel_sine_wave(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """Buffer a sine wave ribbon scrolling across the pixel canvas.
        
        Converted from _apply_pixel_sine_wave for HTP buffer output.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._buffer_static(buffer, fixtures, effect)
            return

        fader_level = getattr(self, '_fader_level', 1.0)
        intensity_scale = (effect.intensity / 100.0) * fader_level
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sy = metrics['scale_y']
        wave_thickness = max(metrics['pixel_radius'] * 1.5, 0.12) / sy if sy > 0.001 else 0.2
        fixture_max_intensity: dict[str, float] = {}

        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            wave_y = 0.5 + 0.35 * math.sin((nx * 3 - phase * 2) * math.pi)
            wave_y += 0.1 * math.sin((nx * 7 + phase * 3) * math.pi)
            dist = abs(ny - wave_y)

            if dist < wave_thickness:
                brightness = (1.0 - (dist / wave_thickness)) ** 0.7
                if getattr(effect, 'rainbow_colors', False):
                    hue = (nx + phase) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                px_scale = brightness * intensity_scale
            else:
                r, g, b = 0, 0, 0
                px_scale = 0.0

            fixture = pixel.get('fixture')
            if fixture:
                fixture_max_intensity[fixture.id] = max(
                    fixture_max_intensity.get(fixture.id, 0.0), px_scale)
            apply_color_to_pixel(buffer, pixel, r, g, b, px_scale)

        intensity_per_fixture = {fid: int(255 * s) for fid, s in fixture_max_intensity.items()}
        set_pixel_fixture_master_dimmers(buffer, fixtures, intensity_per_fixture)

    # =========================================================================
    # End HTP Multi-Effect Methods
    # =========================================================================

    def _send_fixtures_home(self, fixtures=None):
        """Send moving head fixtures to their home positions, blackout others.
        
        Args:
            fixtures: Optional list of fixtures to send home. If None, sends ALL fixtures home.
        """
        # Check if position preview is active - if so, skip ALL pan/tilt changes
        preview_active = self._is_preview_active()
        if preview_active:
            print("[EffectEngine] Position preview active - skipping send_fixtures_home (pan/tilt protected)")
            return
        
        # Channels claimed by trackpad / fixture control — do not overwrite
        fc = self._fixture_control_channels

        target_fixtures = fixtures if fixtures is not None else self.project.fixtures
        print("[EffectEngine] Sending fixtures to home positions...")
        print(f"[EffectEngine] Target fixtures: {len(target_fixtures)} (of {len(self.project.fixtures)} total)")
        
        for fixture in target_fixtures:
            # Skip fixtures under active group fader control
            if self._is_fixture_under_group_fader(fixture):
                continue
            # Skip fixtures under override fader control
            if fixture.id in self._override_fixtures:
                continue

            # Skip entire fixture if ANY of its channels are claimed
            fixture_claimed = any(
                (fixture.universe, fixture.address + i) in fc
                for i in range(fixture.channel_count)
            )
            if fixture_claimed:
                continue

            name = fixture.label or fixture.profile.name
            has_home = fixture.has_home_position
            
            mode = fixture.mode
            if not mode:
                continue
            
            uni = self.artnet.get_universe(fixture.universe)
            
            if not has_home:
                for i in range(len(mode.channels)):
                    uni.set_channel(fixture.address + i, 0)
                continue
            
            # First: Turn off dimmer/shutter
            for i, ch in enumerate(mode.channels):
                ch_type = ch.type.lower()
                addr = fixture.address + i
                if ch_type in ('dimmer', 'intensity', 'master', 'shutter', 'strobe'):
                    uni.set_channel(addr, 0)
            
            # Second: Set pan/tilt speed to slow
            for i, ch in enumerate(mode.channels):
                ch_type = ch.type.lower()
                addr = fixture.address + i
                if ch_type in ('pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'speed'):
                    uni.set_channel(addr, 200)
            
            # Third: Send pan/tilt to home
            for i, ch in enumerate(mode.channels):
                ch_type = ch.type.lower()
                addr = fixture.address + i
                if ch_type == 'pan' and fixture.home_pan is not None:
                    uni.set_channel(addr, fixture.home_pan)
                elif ch_type == 'tilt' and fixture.home_tilt is not None:
                    uni.set_channel(addr, fixture.home_tilt)
        
        print("[EffectEngine] Done sending fixtures home")
    
    def is_running(self) -> bool:
        """Check if an effect is currently running."""
        return self._running
    
    def _send_to_home_positions(self):
        """Send all fixtures to blackout and moving heads to their home positions."""
        print(f"[HTP] _send_to_home_positions called (fixtures={len(self.project.fixtures if self.project else [])})", flush=True)
        # Check if position preview is active - if so, skip pan/tilt changes
        preview_active = self._is_preview_active()
        # Channels claimed by trackpad / fixture control — do not overwrite
        fc = self._fixture_control_channels
        
        for fixture in self.project.fixtures:
            # Skip fixtures under active group fader control
            if self._is_fixture_under_group_fader(fixture):
                continue
            # Skip fixtures under override fader control
            if fixture.id in self._override_fixtures:
                continue
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = self.artnet.get_universe(fixture.universe)
            
            # Blackout this fixture - turn off all intensity/color channels
            for i, ch in enumerate(mode.channels):
                ch_type = ch.type.lower()
                addr = fixture.address + i
                # Skip channels claimed by fixture control / trackpad
                if (fixture.universe, addr) in fc:
                    continue
                # Turn off dimmer, shutter, RGB, strobe
                if ch_type in ('dimmer', 'master', 'intensity', 'shutter', 'strobe', 
                               'red', 'green', 'blue', 'white', 'amber', 'cyan', 'magenta', 'yellow',
                               'cool_white', 'warm_white'):
                    # Skip channels controlled by the visualizer overlay
                    if self._check_overlay_channel(fixture.universe, addr):
                        continue
                    uni.set_channel(addr, 0)
            
            # Move to home position if fixture has one (but NOT if preview is active!)
            if fixture.has_home_position and not preview_active:
                for i, ch in enumerate(mode.channels):
                    ch_type = ch.type.lower()
                    addr = fixture.address + i
                    # Skip channels claimed by fixture control / trackpad
                    if (fixture.universe, addr) in fc:
                        continue
                    if ch_type == 'pan' and fixture.home_pan is not None:
                        uni.set_channel(addr, fixture.home_pan)
                    elif ch_type == 'tilt' and fixture.home_tilt is not None:
                        uni.set_channel(addr, fixture.home_tilt)
    
    def blackout(self):
        """Blackout all fixtures - turn off lights but DON'T move pan/tilt or special effect channels."""
        self._blackout_fixtures(self.project.fixtures)
    
    def _blackout_fixtures(self, fixtures):
        """Blackout specific fixtures - turn off lights but DON'T move pan/tilt or special effect channels.
        
        Skips fixtures that are under active group fader control to prevent
        group faders from being overridden by effect transitions.
        Also skips channels controlled by the visualizer overlay / spatial
        mapper so their live colour output is not blacked out.
        """
        fc = self._fixture_control_channels
        for fixture in fixtures:
            # Skip fixtures under active group fader control
            if self._is_fixture_under_group_fader(fixture):
                continue
            # Skip fixtures under override fader control
            if fixture.id in self._override_fixtures:
                continue
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            uni = self.artnet.get_universe(fixture.universe)
            
            for i, ch in enumerate(mode.channels):
                ch_type = ch.type.lower()
                addr = fixture.address + i
                # Skip channels claimed by fixture control / trackpad
                if (fixture.universe, addr) in fc:
                    continue
                # Skip channels that should preserve manual settings during blackout:
                # - pan/tilt: don't move lights during blackout
                # - effect/gobo/color_wheel/prism: preserve manual effect settings
                # - macro/type/mode: preserve fixture mode settings
                if ch_type in ('pan', 'tilt', 'pan_fine', 'tilt_fine', 'pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'speed',
                              'effect', 'gobo', 'color_wheel', 'prism', 'macro', 'type', 'auto', 'program', 'mode'):
                    continue
                
                # Skip channels controlled by the visualizer
                if self._check_overlay_channel(fixture.universe, addr):
                    continue
                
                # Close shutter to turn off shutter-controlled fixtures
                # Set dimmer and all other intensity channels to 0
                uni.set_channel(addr, 0)
    
    def _buffer_movement(self, buffer: dict, fixtures: list, effect: EffectParameters, phase: float):
        """Buffer pan/tilt movement pattern for HTP execution.
        
        This writes pan/tilt values to the buffer for later merging, similar to _apply_movement_pan_tilt_only
        but targeting a buffer instead of directly writing to Art-Net.
        """
        if not fixtures:
            return
        
        # Use float math for smooth movement
        pan_range = float(effect.pan_max - effect.pan_min)
        tilt_range = float(effect.tilt_max - effect.tilt_min)
        pan_center = float(effect.pan_min) + pan_range / 2.0
        tilt_center = float(effect.tilt_min) + tilt_range / 2.0
        
        # Normalize pattern
        pattern = (effect.movement_pattern or '').lower().replace(' ', '').replace('-', '').replace('_', '')
        
        sweep_patterns = ('sweep', 'scan', 'sidetoside', 'leftright', 'horizontal', 'pansweep', 'wipe', 'pan')
        nod_patterns = ('nod', 'wave', 'updown', 'upanddown', 'vertical', 'tiltwave', 'bob', 'bow', 'headbang', 'tilt')
        circle_patterns = ('circle', 'circular', 'rotate', 'spin', 'orbit', 'around')
        figure8_patterns = ('figure8', 'figureeight', 'infinity', 'eight', 'lemniscate')
        random_patterns = ('random', 'chaos', 'wild', 'crazy', 'ballyhoo', 'party', 'erratic')
        
        position_based_patterns = (
            'wave_sweep', 'wavesweep', 'tilt_wave', 'tiltwave', 'spiral',
            'waterfall', 'converge', 'diverge', 'mirror', 'fan_out', 'fanout',
            'fan_in', 'fanin', 'chase_pan', 'chasepan', 'random_wave', 'randomwave',
            'bounce_wave', 'bouncewave',
            'stagger', 'crossover', 'figure8_wide', 'figure8wide'
        )
        cross_patterns_b = ('cross', 'xpattern', 'plus')
        pendulum_patterns_b = ('pendulum', 'swing', 'metronome')
        zigzag_patterns_b = ('zigzag', 'zag', 'angular', 'sawtooth')
        
        fixture_offset = getattr(effect, 'fixture_offset', 0.25)
        
        for fixture_idx, fixture in enumerate(fixtures):
            fixture_pos_x = getattr(fixture, 'location_x', 0.5)
            fixture_pos_y = getattr(fixture, 'location_y', 0.5)
            
            # Calculate fixture-specific phase
            if pattern in position_based_patterns:
                if pattern in ('waterfall',):
                    position_offset = fixture_pos_y * fixture_offset
                elif pattern in ('mirror',):
                    position_offset = abs(fixture_pos_x - 0.5) * 2 * fixture_offset
                elif pattern in ('converge', 'fan_in', 'fanin'):
                    position_offset = (1.0 - abs(fixture_pos_x - 0.5) * 2) * fixture_offset
                elif pattern in ('diverge', 'fan_out', 'fanout'):
                    position_offset = abs(fixture_pos_x - 0.5) * 2 * fixture_offset
                elif pattern in ('random_wave', 'randomwave'):
                    import random
                    random.seed(fixture_idx * 12345)
                    position_offset = random.random() * fixture_offset
                elif pattern in ('spiral',):
                    position_offset = (fixture_pos_x + fixture_pos_y) / 2 * fixture_offset
                elif pattern in ('stagger',):
                    position_offset = (fixture_idx / max(len(fixtures), 1)) * fixture_offset
                elif pattern in ('crossover',):
                    position_offset = (0.5 - fixture_pos_x) * fixture_offset
                elif pattern in ('figure8_wide', 'figure8wide'):
                    position_offset = fixture_pos_x * fixture_offset
                else:
                    position_offset = fixture_pos_x * fixture_offset
                
                fixture_phase = (phase + position_offset) % 1.0
            else:
                fixture_phase = (phase + fixture_idx / max(len(fixtures), 1) * fixture_offset) % 1.0
            
            # Compute pan/tilt positions
            _2pi = 2.0 * math.pi
            _fp2pi = fixture_phase * _2pi
            _fp_pi = fixture_phase * math.pi

            if pattern in circle_patterns:
                pan_pos = pan_center + (pan_range / 2.0) * math.cos(_fp2pi)
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.sin(_fp2pi)
            elif pattern in figure8_patterns:
                pan_pos = pan_center + (pan_range / 2.0) * math.sin(_fp2pi)
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.sin(fixture_phase * 4.0 * math.pi)
            elif pattern in sweep_patterns:
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = tilt_center + tilt_range * 0.3 * math.sin(_fp_pi)
            elif pattern in nod_patterns:
                pan_pos = pan_center + pan_range * 0.2 * math.sin(_fp_pi)
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.5 + 0.5 * math.sin(_fp2pi))
            elif pattern in random_patterns:
                import random
                random.seed(int(fixture_phase * 10) + fixture_idx * 1000)
                pan_pos = float(random.randint(effect.pan_min, effect.pan_max))
                tilt_pos = float(random.randint(effect.tilt_min, effect.tilt_max))
            elif pattern in cross_patterns_b:
                pan_pos = pan_center + (pan_range / 2.0) * math.sin(_fp2pi)
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.cos(_fp2pi)
            elif pattern in pendulum_patterns_b:
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = tilt_center + tilt_range * 0.15 * math.sin(fixture_phase * 6.0 * math.pi)
            elif pattern in zigzag_patterns_b:
                seg = int(fixture_phase * 4) % 4
                seg_t = (fixture_phase * 4) % 1.0
                if seg == 0:
                    pan_pos = float(effect.pan_min) + pan_range * seg_t
                    tilt_pos = float(effect.tilt_min) + tilt_range * seg_t
                elif seg == 1:
                    pan_pos = float(effect.pan_max) - pan_range * seg_t
                    tilt_pos = float(effect.tilt_min) + tilt_range * seg_t
                elif seg == 2:
                    pan_pos = float(effect.pan_min) + pan_range * seg_t
                    tilt_pos = float(effect.tilt_max) - tilt_range * seg_t
                else:
                    pan_pos = float(effect.pan_max) - pan_range * seg_t
                    tilt_pos = float(effect.tilt_max) - tilt_range * seg_t
            elif pattern in ('wave_sweep', 'wavesweep'):
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = tilt_center + tilt_range * 0.35 * math.sin(_fp_pi)
            elif pattern in ('tilt_wave', 'tiltwave'):
                pan_pos = pan_center + pan_range * 0.25 * math.sin(_fp_pi)
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.5 + 0.5 * math.sin(_fp2pi))
            elif pattern in ('spiral',):
                radius = 0.3 + 0.2 * math.sin(_fp2pi)
                pan_pos = pan_center + pan_range * radius * math.cos(fixture_phase * 6.0 * math.pi)
                tilt_pos = tilt_center + tilt_range * radius * math.sin(fixture_phase * 6.0 * math.pi)
            elif pattern in ('waterfall',):
                pan_pos = pan_center + pan_range * 0.25 * math.sin(_fp_pi * 0.5)
                tilt_pos = float(effect.tilt_min) + tilt_range * fixture_phase
            elif pattern in ('converge',):
                current_pan = float(effect.pan_min) + fixture_pos_x * pan_range
                current_tilt = float(effect.tilt_min) + (1.0 - fixture_phase) * tilt_range * 0.5 + tilt_range * 0.25
                blend = 0.5 + 0.5 * math.sin(_fp2pi)
                pan_pos = current_pan + (pan_center - current_pan) * blend
                tilt_pos = current_tilt + (tilt_center - current_tilt) * blend
            elif pattern in ('diverge',):
                spread_pan = float(effect.pan_min) + fixture_pos_x * pan_range
                spread_tilt = float(effect.tilt_min) + tilt_range * 0.3
                blend = 0.5 + 0.5 * math.sin(_fp2pi)
                pan_pos = pan_center + (spread_pan - pan_center) * blend
                tilt_pos = tilt_center + (spread_tilt - tilt_center) * blend
            elif pattern in ('mirror',):
                mirror_mult = -1.0 if fixture_pos_x < 0.5 else 1.0
                pan_pos = pan_center + (pan_range / 2.0) * mirror_mult * math.sin(_fp2pi)
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.sin(_fp2pi)
            elif pattern in ('fan_out', 'fanout'):
                base_angle = (fixture_pos_x - 0.5) * math.pi
                spread_amount = 0.5 + 0.5 * math.sin(_fp2pi)
                pan_pos = pan_center + (pan_range / 2.0) * math.sin(base_angle) * spread_amount
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.2 + 0.6 * spread_amount)
            elif pattern in ('fan_in', 'fanin'):
                base_angle = (fixture_pos_x - 0.5) * math.pi
                spread_amount = 0.5 - 0.5 * math.sin(_fp2pi)
                pan_pos = pan_center + (pan_range / 2.0) * math.sin(base_angle) * spread_amount
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.2 + 0.6 * (1.0 - spread_amount))
            elif pattern in ('chase_pan', 'chasepan'):
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = tilt_center + tilt_range * 0.1 * math.sin(_fp_pi)
            elif pattern in ('random_wave', 'randomwave'):
                pan_pos = pan_center + (pan_range / 2.0) * math.sin(_fp2pi)
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.cos(_fp2pi)
            elif pattern in ('bounce_wave', 'bouncewave'):
                bounce_phase = fixture_phase * 2.0
                if bounce_phase > 1.0:
                    bounce_phase = 2.0 - bounce_phase
                pan_pos = float(effect.pan_min) + pan_range * bounce_phase
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.sin(bounce_phase * math.pi)
            elif pattern in ('stagger',):
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.5 + 0.5 * math.cos(_fp2pi))
            elif pattern in ('crossover',):
                direction = 1.0 if fixture_pos_x < 0.5 else -1.0
                pan_pos = pan_center + (pan_range / 2.0) * direction * math.sin(_fp2pi)
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.sin(_fp_pi)
            elif pattern in ('figure8_wide', 'figure8wide'):
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.5 + 0.5 * math.sin(fixture_phase * 4.0 * math.pi))
            else:
                # Default to center position
                pan_pos = pan_center
                tilt_pos = tilt_center
            
            # Write to buffer
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = fixture.universe
            for i, channel in enumerate(mode.channels):
                ch_type = channel.type.lower()
                addr = fixture.address + i
                
                if ch_type == 'pan':
                    value = int(max(0, min(255, pan_pos)))
                    buffer[(uni, addr)] = (value, ch_type)
                elif ch_type == 'tilt':
                    value = int(max(0, min(255, tilt_pos)))
                    buffer[(uni, addr)] = (value, ch_type)
                elif ch_type in ('pan_fine', 'tilt_fine'):
                    buffer[(uni, addr)] = (0, ch_type)
                elif ch_type in ('pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'speed'):
                    # Default to fastest (0) so fixtures track software coordinates immediately
                    speed_val = getattr(effect, 'position_cycle_speed', 0)
                    buffer[(uni, addr)] = (speed_val, ch_type)
    
    def _run_static_fader_monitor(self, effect: EffectParameters, fixtures: list, skip_pan_tilt: bool):
        """
        Lightweight monitoring loop for static effects (no movement, no position cycling).
        This allows MIDI faders to control intensity of static presets.
        """
        frame_time = 1.0 / 30  # 30fps is sufficient for fader response
        
        # Small yield to ensure GUI thread has finished setting up fader level
        time.sleep(0.01)
        
        last_fader = getattr(self, '_fader_level', 1.0)
        
        print(f"[Effect] Fader monitor started for static effect, initial fader={last_fader:.2f}")
        
        while not self._stop_event.is_set() and self._running:
            current_fader = getattr(self, '_fader_level', 1.0)
            
            # Check if fader level changed significantly
            if abs(current_fader - last_fader) > 0.01:
                print(f"[Effect] Fader changed {last_fader:.2f} -> {current_fader:.2f}, re-applying static")
                
                # Re-apply the static effect with the new fader level
                if effect.color_palette and len(effect.color_palette) > 0:
                    self._apply_static_with_palette(fixtures, effect, skip_pan_tilt=skip_pan_tilt)
                else:
                    self.apply_static(fixtures, effect.color, effect.intensity, 
                                    color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                    effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                    skip_pan_tilt=skip_pan_tilt,
                                    **self._gobo_kwargs(effect))
                
                last_fader = current_fader
            
            # Sleep until next check
            self._stop_event.wait(frame_time)
        
        print(f"[Effect] Fader monitor stopped")

    def _run_effect_loop(self, effect: EffectParameters, fixtures: list):
        """Main effect loop running in thread."""
        frame_time = 1.0 / 50  # 50fps — must exceed Art-Net send rate (44fps) for smooth movement
        
        print(f"[Effect] Loop started: effect_type={effect.effect_type}, movement_pattern='{effect.movement_pattern}', BPM={effect.speed_bpm}")
        print(f"[Effect] Has color_palette: {len(effect.color_palette) > 0}, has_movement: {bool(effect.movement_pattern and effect.movement_pattern.lower() not in ('none', ''))}")
        
        # Cache mover detection ONCE at the start instead of every frame
        all_movers_cache = []
        all_static_cache = []
        for f in fixtures:
            if self._fixture_has_pan_tilt(f):
                all_movers_cache.append(f)
            else:
                all_static_cache.append(f)
        print(f"[Effect] Pre-cached: {len(all_movers_cache)} movers, {len(all_static_cache)} static fixtures")
        
        # Capture current pan/tilt positions of movers BEFORE any movement is applied
        # so we can smoothly ramp from "where they are now" into the new pattern.
        movement_start_positions = self._capture_current_pan_tilt(all_movers_cache)
        movement_ramp_start = time.time()
        if movement_start_positions:
            print(f"[Effect] Captured {len(movement_start_positions)} mover start positions for smooth ramp-in")
        
        # Track static effect parameters to avoid redundant reapplication
        last_applied_color = None
        last_applied_intensity = None
        last_applied_palette = None
        static_needs_reapply = True  # Apply on first frame
        
        # Track strobe color application for movers (apply once, then only modulate intensity)
        strobe_color_applied_to_movers = False
        last_strobe_speed = effect.speed_bpm  # Track speed changes
        
        # Track phase accumulation for smooth speed changes
        accumulated_phase = 0.0
        last_frame_time = time.time()
        
        # Store original cycle_seconds for scaling (if set)
        original_cycle_seconds = effect.cycle_seconds if effect.cycle_seconds and effect.cycle_seconds > 0 else 0
        original_bpm = effect.speed_bpm if effect.speed_bpm > 0 else 120
        
        # Position cycling tracking (independent overlay feature)
        self._position_cycle_index = 0
        self._position_cycle_time = 0.0
        self._position_cycle_last_time = time.time()
        
        # Small yield to ensure GUI thread has finished setting up fader level
        time.sleep(0.01)
        
        while not self._stop_event.is_set():
            loop_start = time.perf_counter()
            
            # When paused, skip animation updates but keep the loop alive
            if self._paused:
                time.sleep(frame_time)
                last_frame_time = time.time()  # Reset time tracking so we don't jump when resuming
                continue
            
            # Clear per-frame caches for pixel effect tracking
            self._clear_pixel_frame_tracking()
            
            # Use self._current_effect to pick up live parameter changes from update_effect()
            effect = self._current_effect
            if not effect:
                import traceback
                print(f"[Effect] WARNING: _current_effect is None — effect loop exiting!")
                print(f"[Effect]   _running={self._running}, _stop_event.is_set()={self._stop_event.is_set()}")
                print(f"[Effect]   Override fixtures: {list(self._override_fixtures.keys())[:5]}")
                traceback.print_stack()
                break
            
            # Calculate time since last frame
            current_time = time.time()
            delta_time = current_time - last_frame_time
            last_frame_time = current_time
            
            # Calculate speed multiplier from BPM changes
            # This allows the speed slider to affect ALL timing (including cycle_seconds)
            # Also apply the global speed multiplier from the Live Output panel
            current_bpm = max(1, effect.speed_bpm)
            speed_multiplier = (current_bpm / original_bpm if original_bpm > 0 else 1.0) * self._global_speed_multiplier
            
            # Calculate phase increment based on current speed
            # Priority: cycle_seconds > BPM-based calculation
            if original_cycle_seconds > 0:
                # Use explicit cycle time in seconds, but SCALED by speed multiplier
                cycle_duration = original_cycle_seconds / speed_multiplier
            elif effect.effect_type == 'movement':
                # For movement effects, use a much slower time base
                effective_bpm = max(2, effect.speed_bpm / 10)  # Slow down by 10x
                cycle_duration = 60.0 / (effective_bpm * self._global_speed_multiplier)
            elif effect.effect_type == 'chase':
                # For chase/wave effects, slow down so waves are more visible
                effective_bpm = max(2, effect.speed_bpm / 4)  # Slow down by 4x
                cycle_duration = 60.0 / (effective_bpm * self._global_speed_multiplier)
            else:
                cycle_duration = 60.0 / (max(1, effect.speed_bpm) * self._global_speed_multiplier)
            
            # Increment phase based on delta time and current speed
            phase_increment = delta_time / cycle_duration
            accumulated_phase = (accumulated_phase + phase_increment) % 1.0
            
            phase = accumulated_phase
            
            # Check if we should apply movement to moving heads
            # Movement applies to movers for ANY effect type when movement_pattern is set
            # BUT NOT when position cycling is enabled (position cycling takes priority)
            position_cycling_active = getattr(effect, 'position_cycle_enabled', False)
            has_movement = effect.movement_pattern and effect.movement_pattern.lower() not in ('none', '')
            
            # Override handling: skip fixtures claimed by override faders
            # (group faders, programme faders, etc.) so the effect loop
            # doesn't overwrite the fader's DMX values.  Override fixtures
            # are driven directly by their fader callback or by
            # _run_override_effect_loop on a separate thread.
            if self._override_fixtures:
                active_fixtures = [f for f in fixtures if f.id not in self._override_fixtures]
            else:
                active_fixtures = fixtures
            
            # Build a list of ALL movers for movement overlay (pan/tilt
            # still applies to all movers, even overridden, because
            # movement only sets pan/tilt — not colour/intensity/shutter).
            all_movers_for_movement = all_movers_cache
            
            # Update mover/static caches for colour/intensity dispatch
            # (excluding overridden fixtures)
            if self._override_fixtures:
                frame_movers = [f for f in all_movers_cache if f.id not in self._override_fixtures]
                frame_static = [f for f in all_static_cache if f.id not in self._override_fixtures]
            else:
                frame_movers = all_movers_cache
                frame_static = all_static_cache
            
            # --- CRITICAL FIX for jerky movement ---
            # When a movement pattern is active, we must ensure that ONLY the movement logic
            # controls the pan/tilt channels. Other effect types (like 'chase', 'pulse', etc.)
            # should NOT apply their own static color/intensity effects to fixtures that are
            # designated as 'movers' for the current frame.
            #
            # We split the fixtures into two groups:
            # 1. movers: Fixtures with pan/tilt that will be handled by movement logic.
            # 2. non_movers: Fixtures without pan/tilt, which can receive other effects.
            #
            # This prevents a race condition where, for example, _apply_chase() sends a static
            # DMX packet (including pan/tilt=home) to a fixture right before or after
            # _apply_movement_pan_tilt_only() sends a smooth movement update.

            movers = frame_movers if has_movement else []
            non_movers = active_fixtures if not has_movement else [f for f in active_fixtures if f not in movers]

            # Apply the color/intensity effect to ALL non-overridden fixtures
            # Effects like pulse, chase, fade, rainbow already use skip_pan_tilt=True internally,
            # so they won't interfere with movement patterns
            if effect.effect_type == 'pulse':
                self._apply_pulse(active_fixtures, effect, phase)
            elif effect.effect_type == 'chase':
                self._apply_chase(active_fixtures, effect, phase)
            elif effect.effect_type == 'strobe':
                # For strobe with movement: apply differently based on fixture type
                if has_movement:
                    # Non-movers get full strobe (color + intensity)
                    self._apply_strobe(non_movers, effect, phase)
                    # Movers: apply color ONCE, then only modulate intensity
                    if not strobe_color_applied_to_movers:
                        # First frame: set color/gobo/color_wheel for movers (skip pan/tilt)
                        self.apply_static(movers, effect.color, effect.intensity,
                                        color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                        effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                        skip_pan_tilt=True,
                                        **self._gobo_kwargs(effect))
                        strobe_color_applied_to_movers = True
                    # Every frame: modulate intensity for strobe flash
                    self._apply_strobe_intensity_only(movers, effect, phase)
                else:
                    # No movement - apply full strobe to all fixtures
                    self._apply_strobe(active_fixtures, effect, phase)
            elif effect.effect_type == 'fade':
                elapsed = current_time - self._effect_start_time
                self._apply_fade(active_fixtures, effect, elapsed)
            elif effect.effect_type == 'rainbow':
                self._apply_rainbow(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_chase':
                self._apply_pixel_chase(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_rainbow':
                self._apply_pixel_rainbow(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_wipe':
                self._apply_pixel_wipe(active_fixtures, effect, phase)
            # === GEOMETRY EFFECTS (Multi-fixture unified canvas) ===
            elif effect.effect_type == 'geo_hscan':
                self._apply_geo_hscan(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_vscan':
                self._apply_geo_vscan(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_expand_circle':
                self._apply_geo_expand_circle(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_expand_box':
                self._apply_geo_expand_box(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_diagonal':
                self._apply_geo_diagonal(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_ball':
                self._apply_geo_ball(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_multiball':
                self._apply_geo_multiball(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_bounce_line':
                self._apply_geo_bounce_line(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_pong':
                self._apply_geo_pong(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_plasma':
                self._apply_geo_plasma(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_checker':
                self._apply_geo_checker(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_stripes':
                self._apply_geo_stripes(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_matrix':
                self._apply_geo_matrix(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_sparkle':
                self._apply_geo_sparkle(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_stars':
                self._apply_geo_stars(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_fireworks':
                self._apply_geo_fireworks(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_confetti':
                self._apply_geo_confetti(active_fixtures, effect, phase)
            # === NEW GEOMETRY EFFECTS ===
            elif effect.effect_type == 'geo_flying_stars':
                self._apply_geo_flying_stars(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_comet':
                self._apply_geo_comet(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_spiral':
                self._apply_geo_spiral(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_vortex':
                self._apply_geo_vortex(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_heartbeat':
                self._apply_geo_heartbeat(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_lightning':
                self._apply_geo_lightning(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_wave':
                self._apply_geo_wave(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_dna':
                self._apply_geo_dna(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_radar':
                self._apply_geo_radar(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_crosshair':
                self._apply_geo_crosshair(active_fixtures, effect, phase)
            # === GRADIENT & PALETTE EFFECTS ===
            elif effect.effect_type == 'geo_gradient_sweep':
                self._apply_geo_gradient_sweep(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_gradient_vertical':
                self._apply_geo_gradient_vertical(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_gradient_radial':
                self._apply_geo_gradient_radial(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_aurora':
                self._apply_geo_aurora(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_lava':
                self._apply_geo_lava(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_breathing':
                self._apply_geo_breathing(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_ocean_waves':
                self._apply_geo_ocean_waves(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_sunset':
                self._apply_geo_sunset(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_fire_gradient':
                self._apply_geo_fire_gradient(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_galaxy':
                self._apply_geo_galaxy(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_rainbow_flow':
                self._apply_geo_rainbow_flow(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_neon_pulse':
                self._apply_geo_neon_pulse(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_tropical':
                self._apply_geo_tropical(active_fixtures, effect, phase)
            # === SLOW AMBIENT & ARTISTIC EFFECTS ===
            elif effect.effect_type == 'geo_silk':
                self._apply_geo_silk(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_tide':
                self._apply_geo_tide(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_clouds':
                self._apply_geo_clouds(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_mist':
                self._apply_geo_mist(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_candlelight':
                self._apply_geo_candlelight(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_moonlight':
                self._apply_geo_moonlight(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_ripple':
                self._apply_geo_ripple(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_meditation':
                self._apply_geo_meditation(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_dreamscape':
                self._apply_geo_dreamscape(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_northern_lights':
                self._apply_geo_northern_lights(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_waterfall':
                self._apply_geo_waterfall(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_ember':
                self._apply_geo_ember(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_prism':
                self._apply_geo_prism(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_coral':
                self._apply_geo_coral(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_bioluminescence':
                self._apply_geo_bioluminescence(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_zen':
                self._apply_geo_zen(active_fixtures, effect, phase)
            # === RANDOM FADE & DIMMING EFFECTS ===
            elif effect.effect_type == 'geo_random_fade':
                self._apply_geo_random_fade(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_breathing_wave':
                self._apply_geo_breathing_wave(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_twinkle_fade':
                self._apply_geo_twinkle_fade(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_spotlight_wander':
                self._apply_geo_spotlight_wander(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_cascade_dim':
                self._apply_geo_cascade_dim(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_firefly':
                self._apply_geo_firefly(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_rolling_blackout':
                self._apply_geo_rolling_blackout(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_heartbeat_dim':
                self._apply_geo_heartbeat_dim(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_rain_fade':
                self._apply_geo_rain_fade(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_nebula':
                self._apply_geo_nebula(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_lanterns':
                self._apply_geo_lanterns(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_jellyfish':
                self._apply_geo_jellyfish(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_morning_mist':
                self._apply_geo_morning_mist(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_aurora_dim':
                self._apply_geo_aurora_dim(active_fixtures, effect, phase)
            elif effect.effect_type == 'geo_stardust':
                self._apply_geo_stardust(active_fixtures, effect, phase)
            # === PIXEL PICTURE / POSITION PATTERN EFFECTS ===
            elif effect.effect_type == 'pixel_snake':
                self._apply_pixel_snake(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_rain_drops':
                self._apply_pixel_rain_drops(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_sine_wave':
                self._apply_pixel_sine_wave(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_clock':
                self._apply_pixel_clock(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_orbits':
                self._apply_pixel_orbits(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_starfield':
                self._apply_pixel_starfield(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_diamond':
                self._apply_pixel_diamond(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_butterfly':
                self._apply_pixel_butterfly(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_spinner':
                self._apply_pixel_spinner(active_fixtures, effect, phase)
            elif effect.effect_type == 'pixel_ripple_pool':
                self._apply_pixel_ripple_pool(active_fixtures, effect, phase)
            # === UNIFIED ENSEMBLE EFFECTS (All fixtures coordinated) ===
            elif effect.effect_type == 'ensemble_ocean':
                self._apply_ensemble_ocean(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_aurora':
                self._apply_ensemble_aurora(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_breathing':
                self._apply_ensemble_breathing(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_spotlight_dance':
                self._apply_ensemble_spotlight_dance(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_galaxy':
                self._apply_ensemble_galaxy(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_storm':
                self._apply_ensemble_storm(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_fireplace':
                self._apply_ensemble_fireplace(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_midnight':
                self._apply_ensemble_midnight(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_carnival':
                self._apply_ensemble_carnival(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_meditation':
                self._apply_ensemble_meditation_room(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_forest':
                self._apply_ensemble_forest(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_sunset':
                self._apply_ensemble_sunset(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_underwater':
                self._apply_ensemble_underwater(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_lava':
                self._apply_ensemble_lava(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_ice':
                self._apply_ensemble_ice(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_candy':
                self._apply_ensemble_candy(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_neon':
                self._apply_ensemble_neon(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_earth':
                self._apply_ensemble_earth(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_tropical':
                self._apply_ensemble_tropical(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_clockwork':
                self._apply_ensemble_clockwork(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_starfield':
                self._apply_ensemble_starfield(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_heartbeat_sync':
                self._apply_ensemble_heartbeat_sync(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_wave_pool':
                self._apply_ensemble_wave_pool(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_pendulum':
                self._apply_ensemble_pendulum(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_lighthouse':
                self._apply_ensemble_lighthouse(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_jellyfish':
                self._apply_ensemble_jellyfish(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_plasma':
                self._apply_ensemble_plasma(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_rain':
                self._apply_ensemble_rain(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_disco_ball':
                self._apply_ensemble_disco_ball(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_zen_garden':
                self._apply_ensemble_zen_garden(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_volcano':
                self._apply_ensemble_volcano(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_constellation':
                self._apply_ensemble_constellation(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_ballroom':
                self._apply_ensemble_ballroom(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_waterfall':
                self._apply_ensemble_waterfall(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_sunrise':
                self._apply_ensemble_sunrise(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_moonlight':
                self._apply_ensemble_moonlight(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_dreamy':
                self._apply_ensemble_dreamy(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_matrix':
                self._apply_ensemble_matrix(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_inferno':
                self._apply_ensemble_inferno(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_arctic':
                self._apply_ensemble_arctic(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_dance_floor':
                self._apply_ensemble_dance_floor(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_gentle_waves':
                self._apply_ensemble_gentle_waves(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_enchanted':
                self._apply_ensemble_enchanted(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_slow_chase':
                self._apply_ensemble_slow_chase(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_color_wash':
                self._apply_ensemble_color_wash(active_fixtures, effect, phase)
            # === NEW ENSEMBLE EFFECTS (batch 2) ===
            elif effect.effect_type == 'ensemble_solar_flare':
                self._apply_ensemble_solar_flare(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_snowfall':
                self._apply_ensemble_snowfall(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_electric_storm':
                self._apply_ensemble_electric_storm(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_fairy_dust':
                self._apply_ensemble_fairy_dust(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_cyberpunk':
                self._apply_ensemble_cyberpunk(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_desert_mirage':
                self._apply_ensemble_desert_mirage(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_cherry_blossom':
                self._apply_ensemble_cherry_blossom(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_deep_space':
                self._apply_ensemble_deep_space(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_rave':
                self._apply_ensemble_rave(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_vortex':
                self._apply_ensemble_vortex(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_golden_hour':
                self._apply_ensemble_golden_hour(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_tidal_wave':
                self._apply_ensemble_tidal_wave(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_northern_forest':
                self._apply_ensemble_northern_forest(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_thunder_roll':
                self._apply_ensemble_thunder_roll(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_prism':
                self._apply_ensemble_prism(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_campfire':
                self._apply_ensemble_campfire(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_moonrise':
                self._apply_ensemble_moonrise(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_pulse_wave':
                self._apply_ensemble_pulse_wave(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_laser_grid':
                self._apply_ensemble_laser_grid(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_haunted':
                self._apply_ensemble_haunted(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_color_bounce':
                self._apply_ensemble_color_bounce(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_silk_curtain':
                self._apply_ensemble_silk_curtain(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_crystal_cave':
                self._apply_ensemble_crystal_cave(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_neon_rain':
                self._apply_ensemble_neon_rain(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_coral_reef':
                self._apply_ensemble_coral_reef(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_comet':
                self._apply_ensemble_comet(active_fixtures, effect, phase)
            elif effect.effect_type == 'ensemble_rgb_parade':
                self._apply_ensemble_rgb_parade(active_fixtures, effect, phase)
            # === STROBE EFFECTS (Intensity-only geometric patterns) ===
            elif effect.effect_type == 'strobe_hscan':
                self._apply_strobe_hscan(active_fixtures, effect, phase)
            elif effect.effect_type == 'strobe_vscan':
                self._apply_strobe_vscan(active_fixtures, effect, phase)
            elif effect.effect_type == 'strobe_chase':
                self._apply_strobe_chase(active_fixtures, effect, phase)
            elif effect.effect_type == 'strobe_expand':
                self._apply_strobe_expand(active_fixtures, effect, phase)
            elif effect.effect_type == 'strobe_flash':
                self._apply_strobe_flash(active_fixtures, effect, phase)
            elif effect.effect_type == 'strobe_random':
                self._apply_strobe_random(active_fixtures, effect, phase)
            elif effect.effect_type == 'strobe_alternating':
                self._apply_strobe_alternating(active_fixtures, effect, phase)
            elif effect.effect_type == 'strobe_build':
                self._apply_strobe_build(active_fixtures, effect, phase)
            elif effect.effect_type == 'movement':
                # Treat 'movement' as a base look + a pan/tilt overlay.
                # Color/intensity are applied with pan/tilt skipped, then the movement overlay owns position.
                if effect.color_palette and len(effect.color_palette) > 0:
                    self._apply_static_with_palette(active_fixtures, effect, skip_pan_tilt=True)
                else:
                    # Debug: Log color application every 100 frames
                    if phase < 0.01:  # First frame
                        print(f"[Movement] Applying color {effect.color} intensity {effect.intensity}% to {len(active_fixtures)} fixtures")
                    self.apply_static(active_fixtures, effect.color, effect.intensity,
                                    color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                    effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                    skip_pan_tilt=True,
                                    **self._gobo_kwargs(effect))
            elif effect.effect_type == 'macro':
                self._apply_macro(active_fixtures, effect)
            elif effect.effect_type == 'blackout':
                self._apply_blackout(active_fixtures)
            elif effect.effect_type == 'static':
                # This branch handles 'static' effects that have an active animation thread
                # because of a movement pattern or position cycling.
                color_changed = effect.color != last_applied_color
                intensity_changed = effect.intensity != last_applied_intensity
                palette_changed = (effect.color_palette if effect.color_palette else None) != last_applied_palette
                
                # Also check if fader level changed (for MIDI fader control)
                current_fader = getattr(self, '_fader_level', 1.0)
                last_fader = getattr(self, '_last_applied_fader', 1.0)
                fader_changed = abs(current_fader - last_fader) > 0.01

                if color_changed or intensity_changed or palette_changed or fader_changed or static_needs_reapply:
                    # The base color/intensity is applied to ALL fixtures in this case,
                    # but with pan/tilt skipped to avoid conflicts.
                    if effect.color_palette and len(effect.color_palette) > 0:
                        self._apply_static_with_palette(active_fixtures, effect, skip_pan_tilt=True)
                    else:
                        self.apply_static(active_fixtures, effect.color, effect.intensity,
                                        color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                        effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                        skip_pan_tilt=True,
                                        **self._gobo_kwargs(effect))

                    last_applied_color = effect.color
                    last_applied_intensity = effect.intensity
                    last_applied_palette = effect.color_palette if effect.color_palette else None
                    self._last_applied_fader = current_fader
                    static_needs_reapply = False

            # Now, handle position cycling and movement patterns as overlays.
            # IMPORTANT: Movement applies to ALL movers including overridden ones.
            # The override fader only controls colour/intensity — the main effect's
            # movement pattern should continue driving pan/tilt on those fixtures.
            position_cycling_active = getattr(effect, 'position_cycle_enabled', False)
            
            # Compute ramp-in blend factor for smooth movement start
            ramp_blend = self._get_ramp_in_blend(movement_ramp_start)

            if position_cycling_active:
                # Position cycling takes precedence over manual movement patterns,
                # but if there are no usable presets we fall back to movement.
                # Use ALL fixtures (including overridden) so pan/tilt keeps updating.
                applied = self._apply_position_cycle_overlay(fixtures, effect, current_time,
                                                            start_positions=movement_start_positions,
                                                            ramp_blend=ramp_blend)
                if (not applied) and has_movement:
                    # Skip movers under movement-only override (their own loop controls pan/tilt)
                    move_movers = all_movers_for_movement
                    if self._movement_override_movers:
                        move_movers = [m for m in all_movers_for_movement if m.id not in self._movement_override_movers]
                    if move_movers:
                        self._apply_movement_pan_tilt_only(move_movers, effect, phase,
                                                          start_positions=movement_start_positions,
                                                          ramp_blend=ramp_blend)
            elif has_movement:
                # Apply movement pattern to ALL movers (including overridden ones)
                # EXCEPT movers under a movement-only override — their own loop
                # controls pan/tilt so the main loop must leave them alone.
                move_movers = all_movers_for_movement
                if self._movement_override_movers:
                    move_movers = [m for m in all_movers_for_movement if m.id not in self._movement_override_movers]
                if move_movers:
                    self._apply_movement_pan_tilt_only(move_movers, effect, phase,
                                                       start_positions=movement_start_positions,
                                                       ramp_blend=ramp_blend)

            # Finalize pixel fixture master dimmers based on tracked max intensities
            # This ensures fixtures go fully dark when all their pixels are off
            self._finalize_pixel_fixture_dimmers(active_fixtures)

            # Re-assert stored override DMX values so group fader values are
            # never lost — the legacy loop runs at 50 fps and this guarantees
            # that overridden channels are written back every frame.
            if self._override_dmx_values:
                self._reassert_override_dmx()

            # Throttle loop to a stable frame rate and yield to the Art-Net sender thread
            elapsed = time.perf_counter() - loop_start
            sleep_time = frame_time - elapsed
            if sleep_time > 0:
                self._stop_event.wait(sleep_time)
            else:
                # Always yield at least a tiny bit to avoid starving other threads
                self._stop_event.wait(0)
    
    def _run_position_cycle_loop(self, effect: EffectParameters, fixtures: list):
        """Effect loop that cycles through position presets.
        
        This reads position presets LIVE from the project, so if you update
        a position preset, the effect will use the new positions immediately.
        
        If effect.position_cycle_presets is set (list of preset IDs), only those
        presets will be cycled. Otherwise, all presets are cycled.
        """
        frame_time = 1.0 / 50  # 50fps — must exceed Art-Net send rate (44fps)
        position_hold_time = effect.cycle_seconds if effect.cycle_seconds > 0 else 4.0
        
        print(f"[Effect] Position cycle started: hold_time={position_hold_time}s, selected_presets={effect.position_cycle_presets}")
        
        current_preset_index = 0
        time_at_current_position = 0.0
        last_frame_time = time.time()
        pulse_phase = 0.0
        color_phase = 0.0
        
        # Find moving head fixtures
        mover_fixtures = [f for f in fixtures if self._fixture_has_pan_tilt(f)]
        
        # Capture current pan/tilt for smooth ramp-in
        pos_cycle_start_positions = self._capture_current_pan_tilt(mover_fixtures)
        pos_cycle_ramp_start = time.time()
        
        while not self._stop_event.is_set():
            # Read position presets LIVE from project (so updates are reflected)
            all_position_presets = self.project.position_presets
            
            # Filter to only selected presets if specified
            if effect.position_cycle_presets:
                position_presets = [p for p in all_position_presets if p.id in effect.position_cycle_presets]
            else:
                position_presets = all_position_presets
            
            if not position_presets:
                # No presets, just hold still
                self._stop_event.wait(frame_time)
                continue
            
            current_time = time.time()
            delta_time = current_time - last_frame_time
            last_frame_time = current_time
            
            # Apply global speed multiplier to position cycling
            effective_hold_time = position_hold_time / self._global_speed_multiplier
            
            # Accumulate time at current position
            time_at_current_position += delta_time
            
            # Check if it's time to move to next position
            if time_at_current_position >= effective_hold_time:
                time_at_current_position = 0.0
                current_preset_index = (current_preset_index + 1) % len(position_presets)
                print(f"[Effect] Moving to position: {position_presets[current_preset_index].name}")
            
            # Wrap index if presets list changed
            if current_preset_index >= len(position_presets):
                current_preset_index = 0
            
            # Get current position preset
            current_preset = position_presets[current_preset_index]
            
            # Apply pan/tilt from the position preset to movers
            for fixture in mover_fixtures:
                if fixture.id not in current_preset.fixture_positions:
                    continue
                
                pos = current_preset.fixture_positions[fixture.id]
                mode = fixture.profile.get_mode(fixture.mode_name)
                if not mode:
                    continue
                
                uni = self.artnet.get_universe(fixture.universe)
                if not uni:
                    continue
                
                # Compute ramp-in blend for smooth transition
                pos_ramp_blend = self._get_ramp_in_blend(pos_cycle_ramp_start)
                
                for i, ch in enumerate(mode.channels):
                    ch_type = ch.type.lower()
                    addr = fixture.address + i  # 1-indexed for Art-Net
                    
                    if ch_type == 'pan' and 'pan' in pos:
                        blended_pan, _ = self._blend_pan_tilt(
                            fixture.id, pos['pan'], 128,
                            pos_cycle_start_positions, pos_ramp_blend)
                        uni.set_channel(addr, blended_pan)
                    elif ch_type == 'tilt' and 'tilt' in pos:
                        _, blended_tilt = self._blend_pan_tilt(
                            fixture.id, 128, pos['tilt'],
                            pos_cycle_start_positions, pos_ramp_blend)
                        uni.set_channel(addr, blended_tilt)
            
            # Update pulse phase if pulsing (apply global speed multiplier)
            if effect.speed_bpm and effect.speed_bpm > 0:
                pulse_phase += delta_time * effect.speed_bpm * self._global_speed_multiplier / 60.0
                pulse_phase = pulse_phase % 1.0
            
            # Update color phase for rainbow (apply global speed multiplier)
            if getattr(effect, 'rainbow_colors', False):
                color_phase += delta_time * self._global_speed_multiplier / 8.0  # 8 second color cycle at 1x
                color_phase = color_phase % 1.0
            
            # Calculate intensity (with optional pulse)
            if effect.speed_bpm and effect.speed_bpm > 0 and effect.intensity_min < effect.intensity_max:
                intensity_range = effect.intensity_max - effect.intensity_min
                intensity = effect.intensity_min + intensity_range * (0.5 + 0.5 * math.sin(pulse_phase * 2 * math.pi))
            else:
                intensity = effect.intensity
            
            # Calculate color (with optional rainbow)
            if getattr(effect, 'rainbow_colors', False):
                color = self._phase_to_rainbow_color(color_phase)
            else:
                color = effect.color
            
            # Apply color and intensity to fixtures (skip overridden ones)
            r, g, b = hex_to_rgb(color)
            intensity_scale = intensity / 100.0
            override_fids = self._override_fixtures  # snapshot for fast lookup
            
            for fixture in fixtures:
                # Skip fixtures owned by override faders (group faders, etc.)
                # so the position-cycle loop doesn't overwrite fader DMX values.
                if fixture.id in override_fids:
                    continue
                
                mode = fixture.profile.get_mode(fixture.mode_name)
                if not mode:
                    continue
                
                uni = self.artnet.get_universe(fixture.universe)
                if not uni:
                    continue
                
                # Find the best dimmer channel - prefer one named "Dimmer" or "Master"
                first_dimmer_index = -1
                best_dimmer_score = -1
                for idx, ch in enumerate(mode.channels):
                    if ch.type.lower() in ('dimmer', 'intensity', 'master', 'master dimmer'):
                        ch_name = ch.name.lower() if ch.name else ''
                        score = 0
                        if 'master' in ch_name:
                            score = 3
                        elif ch_name in ('dimmer', 'intensity', 'brightness'):
                            score = 2
                        elif 'dim' in ch_name or 'intensity' in ch_name:
                            score = 1
                        if score > best_dimmer_score:
                            best_dimmer_score = score
                            first_dimmer_index = idx
                
                _oc = self._check_overlay_channel
                f_uni = fixture.universe
                for i, channel in enumerate(mode.channels):
                    ch_type = channel.type.lower()
                    addr = fixture.address + i  # 1-indexed for Art-Net
                    
                    if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                        # Only set the FIRST dimmer channel
                        if i == first_dimmer_index and not _oc(f_uni, addr):
                            uni.set_channel(addr, int(255 * intensity_scale))
                    elif ch_type == 'red':
                        if not _oc(f_uni, addr):
                            uni.set_channel(addr, int(r * intensity_scale))
                    elif ch_type == 'green':
                        if not _oc(f_uni, addr):
                            uni.set_channel(addr, int(g * intensity_scale))
                    elif ch_type == 'blue':
                        if not _oc(f_uni, addr):
                            uni.set_channel(addr, int(b * intensity_scale))
                    elif ch_type == 'shutter':
                        if not _oc(f_uni, addr):
                            uni.set_channel(addr, 255)  # Keep shutter open
            
            # Re-assert override DMX values at end of each frame
            if self._override_dmx_values:
                self._reassert_override_dmx()
            
            # Callback for UI (use effective_hold_time for accurate progress)
            if self._on_update:
                self._on_update(time_at_current_position / effective_hold_time)
            
            self._stop_event.wait(frame_time)
    
    def _phase_to_rainbow_color(self, phase: float) -> str:
        """Convert a phase (0-1) to a rainbow color hex string."""
        # HSV to RGB with H = phase * 360
        import colorsys
        r, g, b = colorsys.hsv_to_rgb(phase, 1.0, 1.0)
        return f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}"
    
    def _apply_pulse(self, fixtures: list, effect: EffectParameters, phase: float):
        """Apply pulse effect - fade in/out."""
        # Sine wave for smooth pulse between intensity_min and intensity_max
        intensity_range = effect.intensity_max - effect.intensity_min
        raw_intensity = effect.intensity_min + intensity_range * (0.5 + 0.5 * math.sin(phase * 2 * math.pi))
        
        # Apply master intensity slider as a dimmer (scales the final output)
        intensity = raw_intensity * (effect.intensity / 100.0)
        
        # Check for color palette
        color_palette = getattr(effect, 'color_palette', [])
        
        if color_palette and len(color_palette) > 0:
            # Each fixture gets a different color from palette
            for i, fixture in enumerate(fixtures):
                fixture_color = color_palette[i % len(color_palette)]
                self.apply_static([fixture], fixture_color, int(intensity), 
                                color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                skip_pan_tilt=True,
                                **self._gobo_kwargs(effect))
        else:
            self.apply_static(fixtures, effect.color, int(intensity), 
                            color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                            effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                            skip_pan_tilt=True,
                            **self._gobo_kwargs(effect))
    
    def _apply_chase(self, fixtures: list, effect: EffectParameters, phase: float):
        """Apply chase effect - true wave pattern based on physical position.
        
        For pixel-mapped fixtures, the wave animates across individual pixels (columns/rows)
        within each fixture, creating a flowing wave effect instead of solid on/off.
        
        The wave travels across fixtures based on their actual stage position (location_x or location_y).
        Fixtures at the same position light up together, creating a realistic wave effect.
        
        Direction determines which axis to use:
        - 'forward' = left-to-right (uses location_x, wave moves from 0 to 1)
        - 'reverse' = right-to-left (uses location_x, wave moves from 1 to 0)
        - 'top_down' = top-to-bottom (uses location_y, wave moves from 0 to 1)
        - 'bottom_up' = bottom-to-top (uses location_y, wave moves from 1 to 0)
        - 'bounce' = alternates direction each cycle
        - 'random' = random fixture timing
        """
        if not fixtures:
            return
        
        # Ensure we have valid intensity values (prevent 0 output)
        # Apply master intensity slider as a dimmer (scales the final output)
        # Also apply fader level for MIDI fader control
        fader_level = getattr(self, '_fader_level', 1.0)
        master_scale = (effect.intensity / 100.0) * fader_level
        intensity_max = (effect.intensity_max if effect.intensity_max > 0 else 100) * master_scale
        intensity_min = effect.intensity_min * master_scale
        
        # Check for color palette
        color_palette = getattr(effect, 'color_palette', [])
        
        # Determine which axis to use based on direction
        direction = getattr(effect, 'direction', 'forward')
        use_y_axis = direction in ('top_down', 'bottom_up')
        reverse_wave = direction in ('reverse', 'bottom_up')
        
        # Bounce handling
        wave_phase = phase
        if direction == 'bounce':
            wave_phase = phase * 2
            if wave_phase > 1.0:
                wave_phase = 2.0 - wave_phase
        
        # Wave width - how wide the bright area is (0.3 = 30% of stage width)
        wave_width = 0.35
        
        # Separate pixel-mapped fixtures from regular fixtures
        pixel_fixtures = []
        regular_fixtures = []
        for fixture in fixtures:
            pixel_table = getattr(fixture.profile, 'pixel_channel_table', [])
            if pixel_table and len(pixel_table) > 1:
                pixel_fixtures.append(fixture)
            else:
                regular_fixtures.append(fixture)
        
        # === Handle pixel-mapped fixtures with per-pixel wave animation ===
        # Track fixtures that have had strobe channels turned off
        strobe_processed = set()
        # Track max intensity per fixture for setting master dimmer after all pixels are processed
        fixture_max_intensity: dict[str, float] = {}
        
        for i, fixture in enumerate(pixel_fixtures):
            pixel_table = fixture.profile.pixel_channel_table
            
            # Apply fixture type cap to pixel fixtures
            fixture_type_cap = self._get_fixture_type_cap(fixture)
            print(f"[PixelCap] {fixture.label}: profile.name='{fixture.profile.name}', cap={fixture_type_cap}, caps_dict={list(self._fixture_type_caps.keys())}")
            
            # Get fixture's base position
            if use_y_axis:
                fixture_pos = getattr(fixture, 'location_y', 0.5)
            else:
                fixture_pos = getattr(fixture, 'location_x', 0.5)
            
            if reverse_wave:
                fixture_pos = 1.0 - fixture_pos
            
            # Get color for this fixture
            if color_palette and len(color_palette) > 0:
                color_offset = int(phase * len(fixtures))
                color_index = (i + color_offset) % len(color_palette)
                fixture_color = color_palette[color_index]
            else:
                fixture_color = effect.color
            
            r, g, b = hex_to_rgb(fixture_color)
            
            # Get min/max column or row for normalization
            if use_y_axis:
                positions = [p.get('row', 1) for p in pixel_table]
            else:
                positions = [p.get('col', 1) for p in pixel_table]
            
            min_pos = min(positions) if positions else 1
            max_pos = max(positions) if positions else 1
            pos_range = max(max_pos - min_pos, 1)
            
            # Apply wave to each pixel based on its position within the fixture
            uni = self.artnet.get_universe(fixture.universe)
            if not uni:
                continue
            
            base_addr = fixture.address
            
            # Get mode channels for strobe detection
            mode = fixture.profile.get_mode(fixture.mode_name)
            mode_channels = mode.channels if mode else []
            
            def is_strobe_channel(channel_offset: int) -> bool:
                """Check if a channel offset corresponds to a strobe-type channel."""
                if channel_offset < len(mode_channels):
                    return mode_channels[channel_offset].type.lower() == 'strobe'
                return False
            
            # Turn OFF strobe channels ONCE per fixture
            if fixture.id not in strobe_processed:
                if mode:
                    for ch_idx, ch in enumerate(mode_channels):
                        if ch.type.lower() == 'strobe':
                            uni.set_channel(base_addr + ch_idx, 0)
                strobe_processed.add(fixture.id)
            
            # Initialize max intensity tracking for this fixture
            if fixture.id not in fixture_max_intensity:
                fixture_max_intensity[fixture.id] = 0.0
            
            for pixel in pixel_table:
                # Get pixel's position within fixture (col for horizontal, row for vertical)
                if use_y_axis:
                    pixel_local_pos = pixel.get('row', 1)
                else:
                    pixel_local_pos = pixel.get('col', 1)
                
                # Normalize to 0-1 within fixture
                pixel_norm = (pixel_local_pos - min_pos) / pos_range if pos_range > 0 else 0.5
                
                # Reverse if needed
                if reverse_wave:
                    pixel_norm = 1.0 - pixel_norm
                
                # Combine fixture position with pixel position for global wave coordinate
                # This creates a continuous wave across all fixtures
                # pixel_global_pos ranges based on fixture position + pixel offset within fixture
                fixture_width = 0.15  # How much "width" each fixture occupies in the global space
                pixel_global_pos = fixture_pos + (pixel_norm - 0.5) * fixture_width
                
                # Calculate intensity based on wave position
                if direction == 'random':
                    import random
                    random.seed(int(phase * 1000) // 100 + i + pixel.get('pixel_num', 0))
                    pixel_intensity = intensity_max if random.random() > 0.5 else intensity_min
                else:
                    # Wave position travels from -wave_width to 1+wave_width
                    wave_pos = wave_phase * (1.0 + wave_width * 2) - wave_width
                    
                    # Distance from wave center to this pixel
                    distance = abs(pixel_global_pos - wave_pos)
                    
                    # Intensity based on distance from wave center
                    if distance < wave_width:
                        brightness = 1.0 - (distance / wave_width)
                        pixel_intensity = intensity_min + (intensity_max - intensity_min) * brightness
                    else:
                        pixel_intensity = intensity_min
                
                # Apply fixture type cap as a SCALING FACTOR
                # This scales the intensity proportionally (100% cap = full, 50% cap = half brightness)
                if fixture_type_cap < 1.0:
                    pixel_intensity = pixel_intensity * fixture_type_cap
                
                intensity_scale = pixel_intensity / 100.0
                
                # Track max intensity for this fixture (for master dimmer)
                fixture_max_intensity[fixture.id] = max(fixture_max_intensity[fixture.id], intensity_scale)
                
                # Apply color to this pixel's channels (skip strobe-type and overlay-owned channels!)
                _oc = self._check_overlay_channel
                f_uni = fixture.universe
                if 'red' in pixel and not is_strobe_channel(pixel['red']) and not _oc(f_uni, base_addr + pixel['red']):
                    uni.set_channel(base_addr + pixel['red'], int(r * intensity_scale))
                if 'green' in pixel and not is_strobe_channel(pixel['green']) and not _oc(f_uni, base_addr + pixel['green']):
                    uni.set_channel(base_addr + pixel['green'], int(g * intensity_scale))
                if 'blue' in pixel and not is_strobe_channel(pixel['blue']) and not _oc(f_uni, base_addr + pixel['blue']):
                    uni.set_channel(base_addr + pixel['blue'], int(b * intensity_scale))
                if 'white' in pixel and not is_strobe_channel(pixel['white']) and not _oc(f_uni, base_addr + pixel['white']):
                    # Add some white for brightness
                    white_val = int(min(r, g, b) * intensity_scale * 0.3)
                    uni.set_channel(base_addr + pixel['white'], white_val)
                if 'dimmer' in pixel and not is_strobe_channel(pixel['dimmer']) and not _oc(f_uni, base_addr + pixel['dimmer']):
                    uni.set_channel(base_addr + pixel['dimmer'], int(255 * intensity_scale))
        
        # Set master dimmers for pixel fixtures based on max pixel intensity
        for fixture in pixel_fixtures:
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = self.artnet.get_universe(fixture.universe)
            if not uni:
                continue
            
            pixel_table = fixture.profile.pixel_channel_table or []
            base_addr = fixture.address
            max_intensity = fixture_max_intensity.get(fixture.id, 0.0)
            master_value = int(255 * max_intensity)
            
            for ch_idx, ch in enumerate(mode.channels):
                ch_type = ch.type.lower()
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    is_pixel_dimmer = any(p.get('dimmer') == ch_idx for p in pixel_table)
                    if not is_pixel_dimmer and not self._check_overlay_channel(fixture.universe, base_addr + ch_idx):
                        uni.set_channel(base_addr + ch_idx, master_value)
        
        # === Handle regular (non-pixel) fixtures as before ===
        for i, fixture in enumerate(regular_fixtures):
            # Get fixture's position on the relevant axis
            if use_y_axis:
                fixture_pos = getattr(fixture, 'location_y', 0.5)
            else:
                fixture_pos = getattr(fixture, 'location_x', 0.5)
            
            # Reverse position if needed
            if reverse_wave:
                fixture_pos = 1.0 - fixture_pos
            
            # Calculate this fixture's intensity based on wave position
            if direction == 'random':
                import random
                random.seed(int(phase * 1000) // 100 + i)
                fixture_intensity = intensity_max if random.random() > 0.5 else intensity_min
            else:
                wave_pos = wave_phase * (1.0 + wave_width * 2) - wave_width
                distance = abs(fixture_pos - wave_pos)
                
                if distance < wave_width:
                    brightness = 1.0 - (distance / wave_width)
                    fixture_intensity = intensity_min + (intensity_max - intensity_min) * brightness
                else:
                    fixture_intensity = intensity_min
            
            # Get color for this fixture
            if color_palette and len(color_palette) > 0:
                color_offset = int(phase * len(fixtures))
                color_index = (i + color_offset) % len(color_palette)
                fixture_color = color_palette[color_index]
            else:
                fixture_color = effect.color
            
            self.apply_static([fixture], fixture_color, int(fixture_intensity),
                            color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                            effect_channel_value=getattr(effect, 'color_channel_value', -1),
                            skip_pan_tilt=True,
                            **self._gobo_kwargs(effect))
    
    def _apply_strobe(self, fixtures: list, effect: EffectParameters, phase: float):
        """Apply strobe effect - rapid on/off flashing.
        
        Strobe uses its own faster timing - BPM controls flashes per minute.
        At 600 BPM = 10 flashes per second (typical strobe speed).
        
        Supports intensity_min/max for dimming effect (flashes between min and max).
        
        IMPORTANT: Strobe uses the global speed multiplier for speed control.
        This is what the fader actually updates when in Speed or Fade+Speed mode.
        
        Fader controls speed via _global_speed_multiplier: 0.25x (slow) to 4x (fast)
        """
        # Strobe uses global speed multiplier (this is what the fader updates)
        # Range: 0.25x (slow) to 4x (fast)
        strobe_bpm = max(60, effect.speed_bpm) * self._global_speed_multiplier
        flashes_per_second = strobe_bpm / 60.0
        
        # Calculate strobe phase based on time - this MUST be independent of fader updates
        elapsed = time.time() - self._effect_start_time
        strobe_phase = (elapsed * flashes_per_second) % 1.0
        
        # Quick on/off based on strobe phase - 50% duty cycle
        # Use intensity_min for "off" state and intensity_max for "on" state
        # This allows dimmed strobes (e.g., flashing between 20% and 100%)
        is_on = strobe_phase < 0.5
        raw_intensity = effect.intensity_max if is_on else effect.intensity_min
        
        # Calculate pre-fader intensity (apply master intensity slider as a dimmer)
        # Fader level will be applied in apply_static to keep it consistent
        pre_fader_intensity = int(raw_intensity * (effect.intensity / 100.0))
        
        # Check for color palette
        color_palette = getattr(effect, 'color_palette', [])
        
        if color_palette and len(color_palette) > 0:
            # Each fixture gets a different color from palette
            for i, fixture in enumerate(fixtures):
                fixture_color = color_palette[i % len(color_palette)]
                # apply_static will apply fader level scaling
                self.apply_static([fixture], fixture_color, pre_fader_intensity,
                                color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                skip_pan_tilt=True,
                                **self._gobo_kwargs(effect))
        else:
            # apply_static will apply fader level scaling
            self.apply_static(fixtures, effect.color, pre_fader_intensity,
                            color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                            effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                            skip_pan_tilt=True,
                            **self._gobo_kwargs(effect))
    
    def _apply_strobe_intensity_only(self, fixtures: list, effect: EffectParameters, phase: float):
        """Apply strobe effect to movers - only modulate intensity/shutter.
        
        This minimal version only touches dimmer and shutter channels to avoid
        interfering with pan/tilt movement. Color is already set by the base effect.
        """
        # Strobe uses global speed multiplier (this is what the fader updates)
        strobe_bpm = max(60, effect.speed_bpm) * self._global_speed_multiplier
        flashes_per_second = strobe_bpm / 60.0
        elapsed = time.time() - self._effect_start_time
        strobe_phase = (elapsed * flashes_per_second) % 1.0
        
        # On/off based on phase
        is_on = strobe_phase < 0.5
        raw_intensity = effect.intensity_max if is_on else effect.intensity_min
        intensity = int(raw_intensity * (effect.intensity / 100.0))
        intensity_scale = intensity / 100.0
        
        # Only touch dimmer and shutter - nothing else
        for fixture in fixtures:
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = self.artnet.get_universe(fixture.universe)
            if not uni:
                continue
            
            has_dimmer = any(ch.type.lower() in ('dimmer', 'intensity', 'master', 'master dimmer') 
                           for ch in mode.channels)
            
            first_dimmer_set = False
            for i, channel in enumerate(mode.channels):
                ch_type = channel.type.lower()
                addr = fixture.address + i
                
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    if not first_dimmer_set:
                        uni.set_channel(addr, int(255 * intensity_scale))
                        first_dimmer_set = True
                elif ch_type == 'shutter':
                    value = 255 if has_dimmer else int(255 * intensity_scale)
                    uni.set_channel(addr, value)
                elif ch_type == 'on_off':
                    # On/Off channel: output on_value when intensity > 0, off_value when 0
                    if intensity_scale > 0:
                        uni.set_channel(addr, getattr(channel, 'on_value', 255))
                    else:
                        uni.set_channel(addr, getattr(channel, 'off_value', 0))
    
    def _apply_fade(self, fixtures: list, effect: EffectParameters, elapsed: float):
        """Apply fade effect - transition to target, then hold."""
        transition_time = effect.transition_time or 2.0
        t = min(1.0, elapsed / transition_time)
        
        # Ease-in-out curve
        t = t * t * (3 - 2 * t)
        
        # Fade from black to target color
        intensity = int(effect.intensity * t)
        self.apply_static(fixtures, effect.color, intensity,
                         color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                         effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                         skip_pan_tilt=True,
                         **self._gobo_kwargs(effect))
        
        # Don't stop - just hold at target after fade completes
    
    def _apply_rainbow(self, fixtures: list, effect: EffectParameters, phase: float):
        """Apply rainbow effect - cycle through colors with optional pulse.
        
        Uses color_palette if provided, otherwise uses standard HSV rainbow.
        """
        if not fixtures:
            return
        
        # Get custom color palette or use None for standard rainbow
        color_palette = getattr(effect, 'color_palette', [])

        intensity_min = getattr(effect, 'intensity_min', 0)
        intensity_max = getattr(effect, 'intensity_max', getattr(effect, 'intensity', 100))
        if intensity_min > intensity_max:
            intensity_min, intensity_max = intensity_max, intensity_min

        intensity_range = intensity_max - intensity_min

        # Optional pulse (only if a range is configured)
        if intensity_range > 0:
            raw_intensity = intensity_min + intensity_range * (0.5 + 0.5 * math.sin(phase * 4 * math.pi))
        else:
            raw_intensity = intensity_max
        
        # Apply master intensity slider as a dimmer (scales the final output)
        pulse_intensity = raw_intensity * (effect.intensity / 100.0)
        
        # Debug on first frame
        if phase < 0.02:
            palette_info = f"custom palette ({len(color_palette)} colors)" if color_palette else "standard rainbow"
            print(f"[Rainbow] Starting rainbow effect on {len(fixtures)} fixtures, intensity range: {effect.intensity_min}-{effect.intensity_max}, using {palette_info}")
        
        for i, fixture in enumerate(fixtures):
            # Offset each fixture's color for chase effect
            offset = i / max(len(fixtures), 1)
            
            # Get color - use custom palette if available, otherwise standard rainbow
            if color_palette and len(color_palette) > 0:
                # Cycle through custom palette colors
                # Each fixture gets a different phase offset, and colors shift over time
                palette_pos = (phase + offset) * len(color_palette)
                color_index = int(palette_pos) % len(color_palette)
                color = color_palette[color_index]
                if i == 0:  # Log only first fixture
                    print(f"[Rainbow] Using palette color: index={color_index}, color={color}")
            else:
                color = get_rainbow_color((phase + offset) % 1.0)
                if i == 0:  # Log only first fixture
                    print(f"[Rainbow] Using standard rainbow color at phase={((phase + offset) % 1.0):.3f}")

            
            # Check if fixture has color wheel - if so, cycle through available colors
            mode = fixture.profile.get_mode(fixture.mode_name) if fixture.profile else None
            has_color_wheel = False
            color_wheel_channel = None
            if mode:
                for ch in mode.channels:
                    if ch.type.lower() == 'color_wheel':
                        has_color_wheel = True
                        color_wheel_channel = ch
                        break
            
            if has_color_wheel and color_wheel_channel and color_wheel_channel.color_wheel_colors:
                # Cycle through color wheel colors
                colors = color_wheel_channel.color_wheel_colors
                num_colors = len(colors)
                # Skip white (index 0) for rainbow effect - start from index 1
                if num_colors > 1:
                    color_index = 1 + int((phase + offset) * (num_colors - 1)) % (num_colors - 1)
                else:
                    color_index = 0
                color_wheel_value = colors[color_index].get('value', 0)
                color_name = colors[color_index].get('name', 'unknown')
                
                if phase < 0.02:
                    print(f"[Rainbow] {fixture.label or fixture.profile.name}: Color wheel with {num_colors} colors, selecting index {color_index} = {color_name} (DMX {color_wheel_value})")
                
                # Check if fixture also has RGB channels - if so, use the color there too
                # (some fixtures have both color wheel AND RGB)
                has_rgb = any(ch.type.lower() in ('red', 'green', 'blue') for ch in mode.channels)
                if has_rgb:
                    # Has both color wheel and RGB - send color to RGB channels too
                    self.apply_static([fixture], color, int(pulse_intensity), 
                                    color_wheel_value=color_wheel_value,
                                    skip_pan_tilt=True)
                else:
                    # Color wheel only - use white as the base (color comes from wheel)
                    self.apply_static([fixture], "#ffffff", int(pulse_intensity), 
                                    color_wheel_value=color_wheel_value,
                                    skip_pan_tilt=True)
            else:
                # Use RGB rainbow
                if phase < 0.02:
                    print(f"[Rainbow] {fixture.label or fixture.profile.name}: Using RGB rainbow color {color}")
                self.apply_static([fixture], color, int(pulse_intensity), skip_pan_tilt=True)
    
    def _apply_pixel_chase(self, fixtures: list, effect: EffectParameters, phase: float):
        """Apply pixel chase effect - wave of light across pixel fixtures.
        
        Supports direction:
        - 'forward' / 'backward' = horizontal wave (left-to-right or right-to-left)
        - 'top_down' / 'bottom_up' = vertical wave (top-to-bottom or bottom-to-top)
        """
        # Get all pixels sorted by canvas position
        all_pixels = get_all_pixel_positions(fixtures)
        
        # Debug (first call only)
        if not hasattr(self, '_apply_pixel_chase_debug'):
            self._apply_pixel_chase_debug = True
            pixel_fixtures = [f for f in fixtures if f.profile.is_pixel_fixture]
            cols = set(p.get('col', 1) for p in all_pixels)
            rows = set(p.get('row', 1) for p in all_pixels)
            print(f"[ApplyPixelChase] Total fixtures: {len(fixtures)}, Pixel fixtures: {len(pixel_fixtures)}, Total pixels: {len(all_pixels)}, Columns: {sorted(cols)}, Rows: {sorted(rows)}")
            for pf in pixel_fixtures:
                print(f"  - {pf.label}: {len(pf.profile.pixel_channel_table)} pixels")
        
        if not all_pixels:
            # Fall back to regular chase for non-pixel fixtures
            self._apply_chase(fixtures, effect, phase)
            return
        
        # Use fader-aware intensity scale
        intensity_scale = self._get_effective_intensity_scale(effect)
        intensity_max = (effect.intensity_max if effect.intensity_max > 0 else 100) / 100.0 * intensity_scale
        intensity_min = effect.intensity_min / 100.0 * intensity_scale
        
        color_palette = effect.color_palette if effect.color_palette else [effect.color]
        
        # Determine direction
        direction = getattr(effect, 'direction', 'forward')
        use_y_axis = direction in ('top_down', 'bottom_up')
        reverse = direction in ('backward', 'bottom_up')
        
        if use_y_axis:
            # Vertical wave - use rows
            positions = [p.get('row', 1) for p in all_pixels]
        else:
            # Horizontal wave - use columns
            positions = [p.get('col', 1) for p in all_pixels]
        
        min_pos = min(positions)
        max_pos = max(positions)
        num_positions = max(max_pos - min_pos + 1, 1)
        wave_width = 2.0 / num_positions  # Wave spans ~2 positions
        
        wave_phase = phase
        if reverse:
            wave_phase = 1.0 - phase
        
        for idx, pixel in enumerate(all_pixels):
            if use_y_axis:
                pos = pixel.get('row', 1)
            else:
                pos = pixel.get('col', 1)
            
            norm_pos = (pos - min_pos) / max(num_positions - 1, 1)  # 0.0 to 1.0
            
            wave_pos = wave_phase * (1.0 + wave_width * 2) - wave_width
            dist_from_wave = abs(norm_pos - wave_pos)
            
            if dist_from_wave < wave_width:
                brightness = 1.0 - (dist_from_wave / wave_width)
                pixel_intensity = intensity_min + (intensity_max - intensity_min) * brightness
            else:
                pixel_intensity = intensity_min
            
            color_idx = pos % len(color_palette)  # Color by position
            color = color_palette[color_idx]
            r, g, b = hex_to_rgb(color)
            
            # pixel_intensity is already in 0-1 scale
            self._apply_color_to_pixel(pixel, r, g, b, pixel_intensity)
    
    def _apply_pixel_rainbow(self, fixtures: list, effect: EffectParameters, phase: float):
        """Apply pixel rainbow effect - rainbow colors across pixel fixtures."""
        all_pixels = get_all_pixel_positions(fixtures)
        
        # Debug (first call only)
        if not hasattr(self, '_apply_pixel_rainbow_debug'):
            self._apply_pixel_rainbow_debug = True
            pixel_fixtures = [f for f in fixtures if f.profile.is_pixel_fixture]
            cols = set(p.get('col', 1) for p in all_pixels)
            print(f"[ApplyPixelRainbow] Total fixtures: {len(fixtures)}, Pixel fixtures: {len(pixel_fixtures)}, Total pixels: {len(all_pixels)}, Columns: {sorted(cols)}")
        
        if not all_pixels:
            # Fall back to regular rainbow for non-pixel fixtures
            self._apply_rainbow(fixtures, effect, phase)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use column number for rainbow positioning (more reliable than canvas_x)
        min_col = min(p.get('col', 1) for p in all_pixels)
        max_col = max(p.get('col', 1) for p in all_pixels)
        num_cols = max(max_col - min_col + 1, 1)
        
        for pixel in all_pixels:
            col = pixel.get('col', 1)
            norm_pos = (col - min_col) / max(num_cols - 1, 1)  # 0.0 to 1.0 across columns
            hue = (norm_pos + phase) % 1.0
            color = get_rainbow_color(hue)
            r, g, b = hex_to_rgb(color)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
    
    def _apply_pixel_wipe(self, fixtures: list, effect: EffectParameters, phase: float):
        """Apply pixel wipe effect - color wipe across pixel fixtures."""
        all_pixels = get_all_pixel_positions(fixtures)
        
        # Debug (first call only)
        if not hasattr(self, '_apply_pixel_wipe_debug'):
            self._apply_pixel_wipe_debug = True
            cols = set(p.get('col', 1) for p in all_pixels)
            print(f"[ApplyPixelWipe] Total pixels: {len(all_pixels)}, Columns: {sorted(cols)}")
        
        if not all_pixels:
            # Fall back to static for non-pixel fixtures
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        r, g, b = hex_to_rgb(effect.color)
        
        # Use column number for wipe position (more reliable than canvas_x)
        min_col = min(p.get('col', 1) for p in all_pixels)
        max_col = max(p.get('col', 1) for p in all_pixels)
        col_range = max(max_col - min_col, 1)
        
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        # Wipe threshold - which column should be lit based on phase
        wipe_col = min_col + phase * (col_range + 1)  # +1 to include last column
        
        for pixel in all_pixels:
            col = pixel.get('col', 1)
            if col <= wipe_col:
                self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _get_effective_intensity_scale(self, effect: 'EffectParameters') -> float:
        """Get the effective intensity scale including fader level.
        
        This should be used by all pixel/geometry effects to properly respect fader control.
        Uses thread-local fader level if set (for override loops), otherwise self._fader_level.
        """
        base_intensity = effect.intensity / 100.0
        # Check thread-local first (set by override effect loops)
        fader_level = getattr(self._thread_fader_level, 'value', None)
        if fader_level is None:
            fader_level = getattr(self, '_fader_level', 1.0)
        if fader_level is None:
            fader_level = 1.0
        return base_intensity * fader_level

    def _geo_fallback_static(self, fixtures: list, effect: 'EffectParameters'):
        """Fallback for geo methods when no pixel data is found.

        If the HTP buffer-capture TLS is active (called via _buffer_geo_adapter),
        write to the buffer so the merge loop can still output the static frame.
        Otherwise fall back to direct Art-Net writes (old single-effect path).
        """
        _tls = getattr(self, '_buffer_capture_tls', None)
        if _tls is not None and getattr(_tls, 'active', False):
            self._buffer_static(_tls.buffer, fixtures, effect)
        else:
            self.apply_static(fixtures, effect.color, effect.intensity, skip_pan_tilt=True)

    def _apply_color_to_pixel(self, pixel_info: dict, r: int, g: int, b: int, intensity_scale: float, white: int = 0):
        """Apply a color directly to a pixel's DMX channels via Art-Net.
        
        If a thread-local HTP buffer capture is active (set by _buffer_geo_adapter),
        writes to that buffer instead of Art-Net.  This allows all _apply_geo_*
        methods to work through the HTP merge system without code duplication.
        
        Tracks the maximum intensity seen for each fixture so that the master dimmer
        can be set appropriately at the end of the frame via _finalize_pixel_fixture_dimmers().
        Skips any channels that are typed as 'strobe' in the fixture mode.
        Applies fixture type brightness cap as a scaling factor.
        """
        # ── HTP buffer capture redirect ──────────────────────────────────
        _tls = getattr(self, '_buffer_capture_tls', None)
        if _tls is not None and getattr(_tls, 'active', False):
            buf = _tls.buffer
            fmi = _tls.fixture_max_intensity
            apply_color_to_pixel(buf, pixel_info, r, g, b, intensity_scale, white)
            fixture = pixel_info.get('fixture')
            if fixture:
                fmi[fixture.id] = max(fmi.get(fixture.id, 0.0), intensity_scale)
            return
        # ── End redirect ─────────────────────────────────────────────────

        fixture = pixel_info.get('fixture')
        if not fixture:
            return

        # Skip fixtures under active group/programme fader override
        if fixture.id in self._override_fixtures:
            return
        
        uni_obj = self.artnet.get_universe(fixture.universe)
        if not uni_obj:
            return
        
        # Apply fixture type brightness cap as a scaling factor
        fixture_type_cap = self._get_fixture_type_cap(fixture)
        if fixture_type_cap < 1.0:
            intensity_scale = intensity_scale * fixture_type_cap
        
        # Apply group intensity scaling so group master dimmers affect pixel effects
        group_intensity = self._get_fixture_group_intensity(fixture)
        if group_intensity < 1.0:
            intensity_scale = intensity_scale * group_intensity
        
        base_addr = fixture.address
        
        # Get mode channels to check channel types
        mode = fixture.profile.get_mode(fixture.mode_name)
        mode_channels = mode.channels if mode else []
        
        # Channel types that are safe for pixel effects to write to
        PIXEL_SAFE_TYPES = {'dimmer', 'intensity', 'red', 'green', 'blue', 'white',
                           'warm_white', 'cool_white', 'amber', 'uv', 'master', 'master dimmer'}
        
        def is_safe_pixel_channel(channel_offset: int) -> bool:
            """Check if a channel offset is safe to write pixel data to.
            
            Returns False for strobe, effect, speed, on_off, disabled, etc.
            These should never receive pixel color/dimmer data.
            """
            if channel_offset < len(mode_channels):
                return mode_channels[channel_offset].type.lower() in PIXEL_SAFE_TYPES
            return True  # Unknown channels are allowed (no mode info)
        
        # Check if visualizer overlay or fixture control dialog owns channels
        overlay_channels = self._viz_overlay_channels | self._fixture_control_channels
        fixture_uni = fixture.universe
        
        def is_overlay_owned(channel_offset: int) -> bool:
            """Check if this channel is owned by an external source."""
            if not overlay_channels:
                return False
            return (fixture_uni, base_addr + channel_offset) in overlay_channels
        
        # Apply RGB/RGBW pixel channels (only if channel type is safe for pixel data
        # AND not owned by the visualizer overlay)
        if 'red' in pixel_info and is_safe_pixel_channel(pixel_info['red']) and not is_overlay_owned(pixel_info['red']):
            uni_obj.set_channel(base_addr + pixel_info['red'], int(r * intensity_scale))
        if 'green' in pixel_info and is_safe_pixel_channel(pixel_info['green']) and not is_overlay_owned(pixel_info['green']):
            uni_obj.set_channel(base_addr + pixel_info['green'], int(g * intensity_scale))
        if 'blue' in pixel_info and is_safe_pixel_channel(pixel_info['blue']) and not is_overlay_owned(pixel_info['blue']):
            uni_obj.set_channel(base_addr + pixel_info['blue'], int(b * intensity_scale))
        if 'white' in pixel_info and is_safe_pixel_channel(pixel_info['white']) and not is_overlay_owned(pixel_info['white']):
            uni_obj.set_channel(base_addr + pixel_info['white'], int(white * intensity_scale))
        
        # Handle per-pixel dimmer (for single-channel dimmer pixels)
        # Only write if the actual mode channel at this offset is a dimmer/intensity type
        # AND not owned by the visualizer overlay
        if 'dimmer' in pixel_info and is_safe_pixel_channel(pixel_info['dimmer']) and not is_overlay_owned(pixel_info['dimmer']):
            # For dimmer-only pixels, set dimmer based on RGB brightness
            brightness = max(r, g, b) / 255.0 if max(r, g, b) > 0 else intensity_scale
            uni_obj.set_channel(base_addr + pixel_info['dimmer'], int(255 * brightness * intensity_scale))
        
        # Track max intensity for this fixture (for master dimmer finalization)
        # Initialize tracking dict if needed
        if not hasattr(self, '_pixel_fixture_max_intensity'):
            self._pixel_fixture_max_intensity = {}
        
        fixture_id = fixture.id
        current_max = self._pixel_fixture_max_intensity.get(fixture_id, 0.0)
        self._pixel_fixture_max_intensity[fixture_id] = max(current_max, intensity_scale)
        
        # Turn off strobe channels (once per fixture per frame)
        if not hasattr(self, '_pixel_fixture_strobes_off'):
            self._pixel_fixture_strobes_off = set()
        
        if fixture_id not in self._pixel_fixture_strobes_off:
            if mode:
                for i, ch in enumerate(mode_channels):
                    if ch.type.lower() == 'strobe':
                        uni_obj.set_channel(base_addr + i, 0)
            self._pixel_fixture_strobes_off.add(fixture_id)
    
    def _finalize_pixel_fixture_dimmers(self, fixtures: list):
        """Set fixture-level master dimmers for pixel fixtures that were processed.
        
        Should be called at the end of each frame after all pixels have been processed.
        
        IMPORTANT: The master dimmer is set to 255 (full) when any pixel was written,
        because the pixel RGB values already have intensity_scale applied to them.
        Setting the master dimmer to the intensity would cause DOUBLE-DIMMING
        (50% fader = 50% RGB * 50% master = 25% actual brightness).
        
        Only sets dimmer for fixtures that were actually processed (tracked).
        If a fixture wasn't tracked this frame, we leave its dimmer alone to avoid
        causing flickering.
        """
        if not hasattr(self, '_pixel_fixture_max_intensity'):
            return
        
        for fixture in fixtures:
            if not fixture.profile.is_pixel_fixture:
                continue
            
            # CRITICAL: Only set dimmer if this fixture was actually tracked this frame
            # Otherwise we'd set it to 0 and cause flickering
            if fixture.id not in self._pixel_fixture_max_intensity:
                continue
            
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni_obj = self.artnet.get_universe(fixture.universe)
            if not uni_obj:
                continue
            
            pixel_table = fixture.profile.pixel_channel_table or []
            base_addr = fixture.address
            
            # Get max intensity for this fixture - if > 0, fixture was used
            max_intensity = self._pixel_fixture_max_intensity.get(fixture.id, 0.0)
            # Master dimmer goes to FULL (255) if any pixel was on,
            # because the RGB values already have intensity_scale applied.
            # Set to 0 only if no pixels were on at all.
            master_value = 255 if max_intensity > 0 else 0
            
            # Find and set the fixture's master dimmer channel, on_off, shutter
            for i, ch in enumerate(mode.channels):
                ch_type = ch.type.lower()
                
                if ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                    # Check if this is a per-pixel dimmer
                    is_pixel_dimmer = any(p.get('dimmer') == i for p in pixel_table)
                    if not is_pixel_dimmer:
                        # This is a fixture-level master dimmer
                        uni_obj.set_channel(base_addr + i, master_value)
                elif ch_type == 'on_off':
                    if master_value > 0:
                        uni_obj.set_channel(base_addr + i, getattr(ch, 'on_value', 255))
                    else:
                        uni_obj.set_channel(base_addr + i, getattr(ch, 'off_value', 0))
                elif ch_type == 'shutter':
                    uni_obj.set_channel(base_addr + i, 255 if master_value > 0 else 0)
                elif ch_type == 'strobe':
                    # Keep strobe off during pixel effects
                    uni_obj.set_channel(base_addr + i, 0)
    
    def _clear_pixel_frame_tracking(self):
        """Clear per-frame tracking data for pixel effects.
        
        Should be called at the start of each frame before processing pixels.
        """
        if hasattr(self, '_pixel_fixture_max_intensity'):
            self._pixel_fixture_max_intensity.clear()
        if hasattr(self, '_pixel_fixture_strobes_off'):
            self._pixel_fixture_strobes_off.clear()
        # Also clear old tracking set for backward compatibility
        if hasattr(self, '_pixel_fixture_dimmers_set'):
            self._pixel_fixture_dimmers_set.clear()

    def _apply_intensity_to_strobe(self, strobe_info: dict, intensity: int):
        """Apply intensity directly to a strobe channel via Art-Net."""
        fixture = strobe_info.get('fixture')
        if not fixture:
            return
        
        uni_obj = self.artnet.get_universe(fixture.universe)
        if not uni_obj:
            return
        
        # Apply fixture type brightness cap so MASTER DIMMERS faders affect strobe effects
        fixture_type_cap = self._get_fixture_type_cap(fixture)
        if fixture_type_cap < 1.0:
            intensity = int(intensity * fixture_type_cap)
        
        # Apply group intensity scaling so group master dimmers affect strobe effects
        group_intensity = self._get_fixture_group_intensity(fixture)
        if group_intensity < 1.0:
            intensity = int(intensity * group_intensity)
        
        addr = fixture.address + strobe_info['channel_offset']
        uni_obj.set_channel(addr, int(intensity))
    
    # ==================== GEOMETRY EFFECTS (Multi-fixture unified canvas) ====================
    
    def _get_unified_pixel_canvas(self, fixtures: list) -> tuple:
        """
        Get all pixels from all pixel fixtures as a unified canvas.
        Returns (all_pixels, bounds) where bounds = (min_x, max_x, min_y, max_y).
        Uses canvas_x/canvas_y which respect fixture positions in the venue.
        """
        all_pixels = get_all_pixel_positions(fixtures)
        if not all_pixels:
            return [], (0, 1, 0, 1)
        
        min_x = min(p['canvas_x'] for p in all_pixels)
        max_x = max(p['canvas_x'] for p in all_pixels)
        min_y = min(p['canvas_y'] for p in all_pixels)
        max_y = max(p['canvas_y'] for p in all_pixels)
        
        # Ensure non-zero ranges — expand SYMMETRICALLY so pixels on a
        # collapsed axis normalise to 0.5 (the centre). This is critical for
        # 1-row/1-column fixtures: 2-D effects centre their patterns at
        # (0.5, 0.5), and pixels stuck at 0.0 would fall outside every radius.
        if max_x - min_x < 0.001:
            mid_x = (min_x + max_x) * 0.5
            min_x = mid_x - 0.05
            max_x = mid_x + 0.05
        if max_y - min_y < 0.001:
            mid_y = (min_y + max_y) * 0.5
            min_y = mid_y - 0.05
            max_y = mid_y + 0.05
        
        return all_pixels, (min_x, max_x, min_y, max_y)
    
    def _normalize_pixel_pos(self, pixel: dict, bounds: tuple) -> tuple:
        """Normalize pixel canvas position to 0.0-1.0 range."""
        min_x, max_x, min_y, max_y = bounds
        nx = (pixel['canvas_x'] - min_x) / (max_x - min_x)
        ny = (pixel['canvas_y'] - min_y) / (max_y - min_y)
        return (nx, ny)
    
    def _get_pixel_canvas_metrics(self, all_pixels: list, bounds: tuple) -> dict:
        """Compute canvas metrics for aspect-ratio-aware pixel pattern effects.
        
        Returns a dict with:
          - aspect: width / height ratio of the canvas (>1 = wide, <1 = tall)
          - spacing: approximate average normalized distance between neighbouring pixels
          - scale_x, scale_y: multipliers so that distances in the normalized 0-1
            space are isotropic (equal in physical units).  For a wide layout the
            Y axis is stretched so circles stay circular.
          - pixel_radius: a good default "glow radius" that covers ~2-3 neighbouring
            pixels regardless of layout density.
        """
        min_x, max_x, min_y, max_y = bounds
        range_x = max_x - min_x
        range_y = max_y - min_y
        aspect = range_x / range_y if range_y > 0.0001 else 1.0
        
        # Scale factors: map into a coordinate system where 1 unit = same
        # physical distance in both axes.  We normalise to the LONGER axis
        # so the shorter axis stays within 0..1 and the longer one too.
        if aspect >= 1.0:
            # Wider than tall — X spans 0-1, Y spans 0..(1/aspect)
            scale_x = 1.0
            scale_y = 1.0 / aspect
        else:
            # Taller than wide — Y spans 0-1, X spans 0..aspect
            scale_x = aspect
            scale_y = 1.0
        
        # Estimate average pixel spacing in normalized coords
        num_pixels = len(all_pixels)
        if num_pixels > 1:
            # Use a simple heuristic: the canvas area divided by pixel count
            # gives area per pixel; sqrt gives spacing.
            area = scale_x * scale_y  # effective normalized area
            spacing = (area / num_pixels) ** 0.5
        else:
            spacing = 0.1
        
        # A good glow radius = ~2-3x spacing so each effect element touches
        # several pixels.  Clamped to reasonable bounds.
        pixel_radius = max(0.04, min(0.25, spacing * 3.0))
        
        return {
            'aspect': aspect,
            'scale_x': scale_x,
            'scale_y': scale_y,
            'spacing': spacing,
            'pixel_radius': pixel_radius,
            'num_pixels': num_pixels,
        }
    
    def _apply_geo_hscan(self, fixtures: list, effect: EffectParameters, phase: float):
        """Horizontal scan line across unified pixel canvas."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        line_width = 0.15  # Width of scan line
        
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        # Scan position moves from -line_width to 1+line_width
        scan_pos = -line_width + phase * (1.0 + 2 * line_width)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dist = abs(nx - scan_pos)
            
            if dist < line_width:
                brightness = 1.0 - (dist / line_width)
                
                if getattr(effect, 'rainbow_colors', False):
                    hue = (nx + phase) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_vscan(self, fixtures: list, effect: EffectParameters, phase: float):
        """Vertical scan line across unified pixel canvas."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        line_width = 0.2  # Width of scan line
        
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        scan_pos = -line_width + phase * (1.0 + 2 * line_width)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dist = abs(ny - scan_pos)
            
            if dist < line_width:
                brightness = 1.0 - (dist / line_width)
                
                if getattr(effect, 'rainbow_colors', False):
                    hue = (ny + phase) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_expand_circle(self, fixtures: list, effect: EffectParameters, phase: float):
        """Expanding/contracting circle from center."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        ring_width = 0.15
        
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        # Circle radius expands from 0 to ~1.5 (to cover corners)
        radius = phase * 1.5
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            # Distance from center (0.5, 0.5)
            dist = ((nx - 0.5) ** 2 + (ny - 0.5) ** 2) ** 0.5
            
            ring_dist = abs(dist - radius)
            if ring_dist < ring_width:
                brightness = 1.0 - (ring_dist / ring_width)
                
                if getattr(effect, 'rainbow_colors', False):
                    hue = (dist + phase) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_expand_box(self, fixtures: list, effect: EffectParameters, phase: float):
        """Expanding/contracting box from center."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        edge_width = 0.1
        
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        # Box expands from center
        half_size = phase * 0.75
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            # Chebyshev distance from center
            dist = max(abs(nx - 0.5), abs(ny - 0.5))
            
            edge_dist = abs(dist - half_size)
            if edge_dist < edge_width:
                brightness = 1.0 - (edge_dist / edge_width)
                
                if getattr(effect, 'rainbow_colors', False):
                    hue = (dist + phase) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_diagonal(self, fixtures: list, effect: EffectParameters, phase: float):
        """Diagonal wipe across canvas."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        wipe_width = 0.2
        
        # Diagonal direction: tlbr, trbl, bltr, brtl
        diag_dir = getattr(effect, 'diagonal_direction', 'tlbr')
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Calculate diagonal position based on direction
            if diag_dir == 'tlbr':
                diag_pos = (nx + ny) / 2
            elif diag_dir == 'trbl':
                diag_pos = ((1 - nx) + ny) / 2
            elif diag_dir == 'bltr':
                diag_pos = (nx + (1 - ny)) / 2
            else:  # brtl
                diag_pos = ((1 - nx) + (1 - ny)) / 2
            
            # Wipe position
            wipe_pos = -wipe_width + phase * (1.0 + 2 * wipe_width)
            dist = abs(diag_pos - wipe_pos)
            
            if dist < wipe_width:
                brightness = 1.0 - (dist / wipe_width)
                
                if getattr(effect, 'rainbow_colors', False):
                    hue = (diag_pos + phase) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_ball(self, fixtures: list, effect: EffectParameters, phase: float):
        """Bouncing ball effect."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        ball_radius = 0.15
        
        # Ball bounces using sin waves with different frequencies
        ball_x = 0.5 + 0.4 * math.sin(phase * 2 * math.pi * 1.3)
        ball_y = 0.5 + 0.4 * math.sin(phase * 2 * math.pi * 1.7)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dist = ((nx - ball_x) ** 2 + (ny - ball_y) ** 2) ** 0.5
            
            if dist < ball_radius:
                brightness = 1.0 - (dist / ball_radius)
                
                if getattr(effect, 'rainbow_colors', False):
                    hue = phase % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_multiball(self, fixtures: list, effect: EffectParameters, phase: float):
        """Multiple bouncing balls."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        ball_radius = 0.12
        
        # Multiple balls with different phases
        balls = [
            (0.5 + 0.35 * math.sin(phase * 2 * math.pi * 1.3), 
             0.5 + 0.35 * math.sin(phase * 2 * math.pi * 1.7), 0.0),
            (0.5 + 0.35 * math.sin((phase + 0.33) * 2 * math.pi * 1.5), 
             0.5 + 0.35 * math.sin((phase + 0.33) * 2 * math.pi * 1.2), 0.33),
            (0.5 + 0.35 * math.sin((phase + 0.66) * 2 * math.pi * 1.1), 
             0.5 + 0.35 * math.sin((phase + 0.66) * 2 * math.pi * 1.9), 0.66),
        ]
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            max_brightness = 0
            best_hue = 0
            
            for bx, by, hue_offset in balls:
                dist = ((nx - bx) ** 2 + (ny - by) ** 2) ** 0.5
                if dist < ball_radius:
                    brightness = 1.0 - (dist / ball_radius)
                    if brightness > max_brightness:
                        max_brightness = brightness
                        best_hue = (phase + hue_offset) % 1.0
            
            if max_brightness > 0:
                color = get_rainbow_color(best_hue)
                r, g, b = hex_to_rgb(color)
                self._apply_color_to_pixel(pixel, r, g, b, max_brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_bounce_line(self, fixtures: list, effect: EffectParameters, phase: float):
        """Bouncing line (horizontal or vertical)."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        line_width = 0.12
        
        # Bounce using absolute sin (ping-pong)
        bounce_pos = abs(math.sin(phase * math.pi))
        
        orientation = getattr(effect, 'line_orientation', 'h')
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            if orientation == 'h':
                dist = abs(ny - bounce_pos)
            else:
                dist = abs(nx - bounce_pos)
            
            if dist < line_width:
                brightness = 1.0 - (dist / line_width)
                r, g, b = hex_to_rgb(effect.color)
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_pong(self, fixtures: list, effect: EffectParameters, phase: float):
        """Pong-style bouncing ball with trails."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        ball_radius = 0.1
        
        # Classic pong diagonal bounce
        ball_x = abs(math.sin(phase * math.pi * 2.3))
        ball_y = abs(math.sin(phase * math.pi * 1.7))
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dist = ((nx - ball_x) ** 2 + (ny - ball_y) ** 2) ** 0.5
            
            if dist < ball_radius:
                brightness = 1.0 - (dist / ball_radius)
                r, g, b = hex_to_rgb(effect.color)
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_plasma(self, fixtures: list, effect: EffectParameters, phase: float):
        """Plasma/lava lamp style organic flow."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Multiple overlapping sine waves create plasma effect
            v = math.sin(nx * 10 + phase * 6)
            v += math.sin((ny * 10 + phase * 4))
            v += math.sin((nx * 5 + ny * 5 + phase * 5))
            v += math.sin(((nx * nx + ny * ny) ** 0.5 * 10 + phase * 3))
            
            # Normalize to 0-1
            v = (v + 4) / 8
            
            hue = (v + phase) % 1.0
            color = get_rainbow_color(hue)
            r, g, b = hex_to_rgb(color)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
    
    def _apply_geo_checker(self, fixtures: list, effect: EffectParameters, phase: float):
        """Checkerboard pattern, optionally animated."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        checker_size = 4  # Number of checker cells
        
        animate = getattr(effect, 'animate', False)
        offset = int(phase * 2) if animate else 0
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            cx = int(nx * checker_size) + offset
            cy = int(ny * checker_size)
            
            if (cx + cy) % 2 == 0:
                r, g, b = hex_to_rgb(effect.color)
                self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_stripes(self, fixtures: list, effect: EffectParameters, phase: float):
        """Stripe pattern (horizontal or vertical)."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        stripe_count = 4
        
        orientation = getattr(effect, 'line_orientation', 'h')
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            if orientation == 'h':
                stripe_idx = int(ny * stripe_count)
            else:
                stripe_idx = int(nx * stripe_count)
            
            if stripe_idx % 2 == 0:
                r, g, b = hex_to_rgb(effect.color)
                self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_matrix(self, fixtures: list, effect: EffectParameters, phase: float):
        """Matrix-style falling rain."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        import random
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use pixel col to seed different drop patterns
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            col = pixel.get('col', 1)
            
            # Each column has drops at different offsets
            drop_speed = 1.5 + (col % 3) * 0.3
            drop_offset = (col * 0.17) % 1.0
            drop_pos = ((phase * drop_speed) + drop_offset) % 1.0
            
            # Tail length
            tail_length = 0.3
            dist = (drop_pos - ny) % 1.0
            
            if dist < tail_length:
                brightness = 1.0 - (dist / tail_length)
                
                if getattr(effect, 'rainbow_colors', False):
                    hue = (col * 0.1 + phase) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_sparkle(self, fixtures: list, effect: EffectParameters, phase: float):
        """Random sparkle/twinkle effect."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use frame number for randomness that changes over time
        frame = int(phase * 100) % 100
        
        for idx, pixel in enumerate(all_pixels):
            # Pseudo-random based on pixel index and frame
            seed = (idx * 7 + frame * 13) % 100
            
            if seed < 15:  # ~15% of pixels lit at any time
                brightness = 0.5 + (seed % 50) / 100.0
                
                if getattr(effect, 'rainbow_colors', False):
                    hue = (seed / 100.0 + phase) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_stars(self, fixtures: list, effect: EffectParameters, phase: float):
        """Twinkling stars effect."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        for idx, pixel in enumerate(all_pixels):
            # Each pixel has its own twinkle phase
            pixel_phase = (phase + idx * 0.07) % 1.0
            
            # Slow sine-based twinkle
            brightness = (math.sin(pixel_phase * 2 * math.pi) + 1) / 2
            brightness = brightness ** 2  # Make dimming more pronounced
            
            r, g, b = hex_to_rgb(effect.color)
            self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
    
    def _apply_geo_fireworks(self, fixtures: list, effect: EffectParameters, phase: float):
        """Fireworks burst effect."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Firework burst at center, expanding outward then fading
        burst_phase = phase % 0.5  # Two bursts per cycle
        burst_radius = burst_phase * 2  # Expand quickly
        fade = max(0, 1.0 - burst_phase * 3)  # Fade out
        
        # Center position varies
        cx = 0.3 + (int(phase * 2) % 2) * 0.4  # Alternate left/right
        cy = 0.4 + (int(phase * 3) % 2) * 0.2
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dist = ((nx - cx) ** 2 + (ny - cy) ** 2) ** 0.5
            
            ring_dist = abs(dist - burst_radius)
            ring_width = 0.1
            
            if ring_dist < ring_width and fade > 0:
                brightness = (1.0 - ring_dist / ring_width) * fade
                
                hue = (dist * 3 + phase) % 1.0
                color = get_rainbow_color(hue)
                r, g, b = hex_to_rgb(color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_confetti(self, fixtures: list, effect: EffectParameters, phase: float):
        """Falling confetti effect."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        for idx, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            col = pixel.get('col', 1)
            
            # Each column has confetti falling at different speeds
            speed = 0.8 + (col % 5) * 0.15
            offset = (col * 0.23 + idx * 0.07) % 1.0
            fall_pos = ((phase * speed) + offset) % 1.0
            
            # Small pieces
            piece_size = 0.08
            dist = abs(fall_pos - ny)
            
            if dist < piece_size:
                brightness = 1.0 - (dist / piece_size)
                
                # Random colors per piece
                hue = ((col * 0.13 + idx * 0.07) % 1.0)
                color = get_rainbow_color(hue)
                r, g, b = hex_to_rgb(color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_flying_stars(self, fixtures: list, effect: EffectParameters, phase: float):
        """Flying stars that shoot across the canvas with trails."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Multiple stars at different speeds and angles
        num_stars = 5
        star_trails = []
        
        for i in range(num_stars):
            # Each star has different timing and trajectory
            star_phase = (phase * (1.0 + i * 0.3) + i * 0.2) % 1.0
            
            # Stars fly from different edges
            if i % 4 == 0:  # Left to right
                sx = -0.2 + star_phase * 1.4
                sy = 0.2 + (i * 0.15) % 0.6
                angle = 0
            elif i % 4 == 1:  # Right to left
                sx = 1.2 - star_phase * 1.4
                sy = 0.3 + (i * 0.12) % 0.5
                angle = math.pi
            elif i % 4 == 2:  # Top to bottom diagonal
                sx = -0.1 + star_phase * 1.2
                sy = -0.1 + star_phase * 1.2
                angle = math.pi / 4
            else:  # Bottom to top diagonal
                sx = 1.1 - star_phase * 1.2
                sy = 1.1 - star_phase * 1.2
                angle = -3 * math.pi / 4
            
            star_trails.append((sx, sy, i))
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            max_brightness = 0
            best_hue = 0
            
            for sx, sy, star_idx in star_trails:
                dist = ((nx - sx) ** 2 + (ny - sy) ** 2) ** 0.5
                
                # Star head (bright)
                head_radius = 0.08
                # Tail (fading)
                tail_radius = 0.25
                
                if dist < head_radius:
                    brightness = 1.0
                elif dist < tail_radius:
                    brightness = (1.0 - (dist - head_radius) / (tail_radius - head_radius)) * 0.6
                else:
                    brightness = 0
                
                if brightness > max_brightness:
                    max_brightness = brightness
                    best_hue = (star_idx * 0.2 + phase) % 1.0
            
            if max_brightness > 0:
                if getattr(effect, 'rainbow_colors', False):
                    color = get_rainbow_color(best_hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                self._apply_color_to_pixel(pixel, r, g, b, max_brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_comet(self, fixtures: list, effect: EffectParameters, phase: float):
        """Single comet with long glowing tail sweeping across."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Comet moves in a curved path
        comet_x = phase
        comet_y = 0.5 + 0.3 * math.sin(phase * 2 * math.pi)
        
        if effect.direction == 'backward':
            comet_x = 1.0 - comet_x
        
        # Tail direction (opposite of movement)
        tail_length = 0.4
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Distance from comet head
            head_dist = ((nx - comet_x) ** 2 + (ny - comet_y) ** 2) ** 0.5
            
            # Check if in tail (behind the comet)
            tail_dist = comet_x - nx  # Positive when pixel is behind comet
            
            brightness = 0
            if head_dist < 0.08:
                # Bright head
                brightness = 1.0
            elif tail_dist > 0 and tail_dist < tail_length:
                # In the tail - check vertical proximity
                vert_dist = abs(ny - comet_y)
                tail_width = 0.15 * (1.0 - tail_dist / tail_length)  # Tail narrows
                if vert_dist < tail_width:
                    brightness = (1.0 - tail_dist / tail_length) * (1.0 - vert_dist / tail_width) * 0.7
            
            if brightness > 0:
                # Gradient from white head to colored tail
                if head_dist < 0.08:
                    r, g, b = 255, 255, 255  # White head
                else:
                    r, g, b = hex_to_rgb(effect.color)
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_spiral(self, fixtures: list, effect: EffectParameters, phase: float):
        """Rotating spiral pattern from center."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        cx, cy = 0.5, 0.5  # Center
        num_arms = 3
        arm_width = 0.3
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Convert to polar coordinates
            dx = nx - cx
            dy = ny - cy
            dist = (dx * dx + dy * dy) ** 0.5
            angle = math.atan2(dy, dx)
            
            # Spiral: angle offset based on distance and animation
            spiral_angle = angle - dist * 4 + phase * 2 * math.pi
            
            # Check if in one of the spiral arms
            arm_phase = (spiral_angle * num_arms / (2 * math.pi)) % 1.0
            
            if arm_phase < arm_width or arm_phase > (1.0 - arm_width):
                brightness = 1.0 - dist  # Fade toward edges
                brightness = max(0, brightness)
                
                if getattr(effect, 'rainbow_colors', False):
                    hue = (angle / (2 * math.pi) + phase) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_vortex(self, fixtures: list, effect: EffectParameters, phase: float):
        """Swirling vortex pulling toward center."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        cx, cy = 0.5, 0.5
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            dx = nx - cx
            dy = ny - cy
            dist = (dx * dx + dy * dy) ** 0.5
            angle = math.atan2(dy, dx)
            
            # Vortex: brightness pulses inward with rotation
            vortex_phase = (dist * 5 - phase * 2 + angle / math.pi) % 1.0
            
            if vortex_phase < 0.4:
                brightness = 1.0 - vortex_phase / 0.4
                
                hue = (dist + phase) % 1.0
                color = get_rainbow_color(hue)
                r, g, b = hex_to_rgb(color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_heartbeat(self, fixtures: list, effect: EffectParameters, phase: float):
        """Pulsing heart shape."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Heartbeat rhythm: quick double-pulse then pause
        beat_phase = phase * 2 % 1.0
        if beat_phase < 0.15:
            pulse = beat_phase / 0.15
        elif beat_phase < 0.3:
            pulse = 1.0 - (beat_phase - 0.15) / 0.15
        elif beat_phase < 0.4:
            pulse = (beat_phase - 0.3) / 0.1 * 0.7
        elif beat_phase < 0.55:
            pulse = 0.7 - (beat_phase - 0.4) / 0.15 * 0.7
        else:
            pulse = 0
        
        heart_size = 0.3 + pulse * 0.15
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Heart shape equation (cardioid-ish)
            hx = (nx - 0.5) / heart_size
            hy = (0.6 - ny) / heart_size  # Flip and offset Y
            
            # Simplified heart check
            heart_val = (hx * hx + hy * hy - 1) ** 3 - hx * hx * hy * hy * hy
            
            if heart_val < 0:
                brightness = min(1.0, pulse + 0.3)
                r, g, b = hex_to_rgb(effect.color)
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_lightning(self, fixtures: list, effect: EffectParameters, phase: float):
        """Lightning bolt strikes."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Lightning strikes at specific phases
        strike_phase = phase * 3 % 1.0
        
        if strike_phase < 0.1:
            # Quick bright flash
            flash_brightness = 1.0
        elif strike_phase < 0.15:
            flash_brightness = 0.3
        elif strike_phase < 0.2:
            flash_brightness = 0.8
        elif strike_phase < 0.3:
            flash_brightness = 0.1 - (strike_phase - 0.2) / 0.1 * 0.1
        else:
            flash_brightness = 0
        
        # Lightning bolt path (jagged vertical line)
        bolt_x = 0.3 + (int(phase * 5) % 3) * 0.2  # Different positions
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Jagged bolt path
            jag = math.sin(ny * 20 + phase * 10) * 0.08
            bolt_dist = abs(nx - bolt_x - jag)
            
            if bolt_dist < 0.06 and flash_brightness > 0:
                brightness = flash_brightness * (1.0 - bolt_dist / 0.06)
                # Lightning is white/blue
                r, g, b = 200, 200, 255
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            elif flash_brightness > 0.5:
                # Ambient flash during strike
                r, g, b = 100, 100, 150
                self._apply_color_to_pixel(pixel, r, g, b, 0.2 * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_wave(self, fixtures: list, effect: EffectParameters, phase: float):
        """Ocean wave pattern."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Wave equation - multiple overlapping waves
            wave1 = math.sin(nx * 8 + phase * 6) * 0.15
            wave2 = math.sin(nx * 5 - phase * 4) * 0.1
            wave_height = 0.5 + wave1 + wave2
            
            # Pixel is lit if below wave line
            if ny > wave_height:
                depth = (ny - wave_height) / (1.0 - wave_height)
                brightness = 1.0 - depth * 0.5  # Darker toward bottom
                
                # Blue gradient for water
                r = int(30 * (1.0 - depth))
                g = int(100 + 50 * (1.0 - depth))
                b = int(200 + 55 * (1.0 - depth))
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_dna(self, fixtures: list, effect: EffectParameters, phase: float):
        """DNA double helix pattern."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        helix_width = 0.08
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Two helices rotating around center
            helix1_x = 0.5 + 0.25 * math.sin(ny * 8 + phase * 4)
            helix2_x = 0.5 + 0.25 * math.sin(ny * 8 + phase * 4 + math.pi)
            
            dist1 = abs(nx - helix1_x)
            dist2 = abs(nx - helix2_x)
            
            brightness = 0
            hue = 0
            
            if dist1 < helix_width:
                brightness = 1.0 - dist1 / helix_width
                hue = 0.0  # Red strand
            elif dist2 < helix_width:
                brightness = 1.0 - dist2 / helix_width
                hue = 0.6  # Blue strand
            
            # Connecting rungs between helices
            rung_spacing = 0.15
            rung_y = (ny % rung_spacing) / rung_spacing
            if abs(rung_y - 0.5) < 0.1:
                if min(helix1_x, helix2_x) < nx < max(helix1_x, helix2_x):
                    brightness = max(brightness, 0.5)
                    hue = 0.15  # Yellow rungs
            
            if brightness > 0:
                color = get_rainbow_color(hue)
                r, g, b = hex_to_rgb(color)
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_radar(self, fixtures: list, effect: EffectParameters, phase: float):
        """Radar sweep effect."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        cx, cy = 0.5, 0.5
        sweep_angle = phase * 2 * math.pi
        sweep_width = 0.5  # Width of the radar beam in radians
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            dx = nx - cx
            dy = ny - cy
            dist = (dx * dx + dy * dy) ** 0.5
            pixel_angle = math.atan2(dy, dx)
            
            # Angle difference (handle wraparound)
            angle_diff = (pixel_angle - sweep_angle + math.pi) % (2 * math.pi) - math.pi
            
            if 0 < angle_diff < sweep_width:
                # In the sweep beam - fade based on how far behind the leading edge
                brightness = 1.0 - angle_diff / sweep_width
                brightness *= (1.0 - dist * 0.5)  # Fade toward edges
                
                r, g, b = hex_to_rgb(effect.color)
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_geo_crosshair(self, fixtures: list, effect: EffectParameters, phase: float):
        """Moving crosshair/targeting reticle."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Crosshair moves around
        cx = 0.5 + 0.3 * math.sin(phase * 2 * math.pi)
        cy = 0.5 + 0.3 * math.cos(phase * 2 * math.pi * 0.7)
        
        line_width = 0.04
        circle_radius = 0.15
        circle_width = 0.03
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Check if on crosshair lines or circle
            on_h_line = abs(ny - cy) < line_width and abs(nx - cx) > circle_radius * 0.5
            on_v_line = abs(nx - cx) < line_width and abs(ny - cy) > circle_radius * 0.5
            
            dist = ((nx - cx) ** 2 + (ny - cy) ** 2) ** 0.5
            on_circle = abs(dist - circle_radius) < circle_width
            
            if on_h_line or on_v_line or on_circle:
                r, g, b = hex_to_rgb(effect.color)
                self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    # ==================== GRADIENT & COLOR PALETTE EFFECTS ====================
    
    # Color palette definitions - curated for smooth, beautiful transitions
    GRADIENT_PALETTES = {
        'sunset': [(255, 94, 58), (255, 149, 0), (255, 204, 0), (255, 45, 85), (175, 82, 222)],
        'ocean': [(0, 119, 182), (0, 180, 216), (144, 224, 239), (202, 240, 248), (72, 202, 228)],
        'forest': [(27, 94, 32), (56, 142, 60), (102, 187, 106), (165, 214, 167), (200, 230, 201)],
        'aurora': [(0, 255, 136), (0, 212, 255), (138, 43, 226), (255, 0, 255), (0, 255, 200)],
        'lava': [(255, 69, 0), (255, 140, 0), (255, 215, 0), (255, 99, 71), (178, 34, 34)],
        'candy': [(255, 105, 180), (255, 182, 193), (255, 20, 147), (219, 112, 147), (199, 21, 133)],
        'ice': [(176, 224, 230), (173, 216, 230), (135, 206, 250), (70, 130, 180), (100, 149, 237)],
        'neon': [(57, 255, 20), (255, 20, 147), (0, 255, 255), (255, 255, 0), (255, 0, 255)],
        'pastel': [(255, 179, 186), (255, 223, 186), (255, 255, 186), (186, 255, 201), (186, 225, 255)],
        'fire': [(255, 0, 0), (255, 69, 0), (255, 140, 0), (255, 215, 0), (255, 255, 100)],
        'galaxy': [(75, 0, 130), (138, 43, 226), (148, 0, 211), (186, 85, 211), (218, 112, 214)],
        'tropical': [(255, 87, 51), (255, 195, 0), (0, 230, 118), (0, 184, 212), (255, 64, 129)],
        'midnight': [(25, 25, 112), (65, 105, 225), (100, 149, 237), (123, 104, 238), (147, 112, 219)],
        'earth': [(139, 90, 43), (160, 82, 45), (210, 105, 30), (184, 134, 11), (218, 165, 32)],
        'rainbow': [(255, 0, 0), (255, 127, 0), (255, 255, 0), (0, 255, 0), (0, 0, 255), (75, 0, 130), (148, 0, 211)],
    }
    
    def _interpolate_palette_color(self, palette: list, position: float) -> tuple:
        """Smoothly interpolate between colors in a palette based on position (0-1)."""
        import math
        position = position % 1.0  # Wrap around
        num_colors = len(palette)
        scaled_pos = position * num_colors
        idx1 = int(scaled_pos) % num_colors
        idx2 = (idx1 + 1) % num_colors
        blend = scaled_pos - int(scaled_pos)
        
        # Smooth easing for more pleasing transitions
        blend = (1 - math.cos(blend * math.pi)) / 2
        
        r = int(palette[idx1][0] * (1 - blend) + palette[idx2][0] * blend)
        g = int(palette[idx1][1] * (1 - blend) + palette[idx2][1] * blend)
        b = int(palette[idx1][2] * (1 - blend) + palette[idx2][2] * blend)
        
        return (r, g, b)
    
    def _apply_geo_gradient_sweep(self, fixtures: list, effect: EffectParameters, phase: float):
        """Smooth gradient sweep across the canvas - horizontal flow."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'sunset')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['sunset'])
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            # Slow horizontal sweep with the gradient
            color_pos = (nx + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
    
    def _apply_geo_gradient_vertical(self, fixtures: list, effect: EffectParameters, phase: float):
        """Smooth gradient sweep - vertical flow."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'ocean')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['ocean'])
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            color_pos = (ny + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
    
    def _apply_geo_gradient_radial(self, fixtures: list, effect: EffectParameters, phase: float):
        """Radial gradient emanating from center."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'aurora')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['aurora'])
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dist = ((nx - 0.5) ** 2 + (ny - 0.5) ** 2) ** 0.5
            color_pos = (dist * 2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
    
    def _apply_geo_aurora(self, fixtures: list, effect: EffectParameters, phase: float):
        """Northern lights / aurora borealis effect - flowing curtains of color."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['aurora']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Create flowing curtain effect
            wave1 = math.sin((nx * 3 + phase * 2) * math.pi) * 0.3
            wave2 = math.sin((nx * 5 - phase * 1.5) * math.pi) * 0.2
            wave3 = math.sin((nx * 2 + phase * 0.7) * math.pi) * 0.15
            
            # Vertical intensity falloff (aurora stronger at top)
            v_intensity = 1.0 - ny * 0.6
            
            # Combine waves for color position
            color_pos = (nx * 0.5 + wave1 + wave2 + phase * 0.3) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Apply wave-based brightness variation
            brightness = max(0.3, min(1.0, 0.7 + wave1 + wave3)) * v_intensity
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_lava(self, fixtures: list, effect: EffectParameters, phase: float):
        """Lava lamp style slowly morphing blobs."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['lava']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Create slowly moving blob centers
            blob1_x = 0.3 + 0.2 * math.sin(phase * 2 * math.pi * 0.5)
            blob1_y = 0.5 + 0.3 * math.sin(phase * 2 * math.pi * 0.3)
            blob2_x = 0.7 + 0.2 * math.sin(phase * 2 * math.pi * 0.4 + 1)
            blob2_y = 0.5 + 0.3 * math.cos(phase * 2 * math.pi * 0.35)
            blob3_x = 0.5 + 0.25 * math.cos(phase * 2 * math.pi * 0.25)
            blob3_y = 0.3 + 0.2 * math.sin(phase * 2 * math.pi * 0.6)
            
            # Distance to each blob (inverted for brightness)
            d1 = 1.0 / (1.0 + 10 * ((nx - blob1_x) ** 2 + (ny - blob1_y) ** 2))
            d2 = 1.0 / (1.0 + 10 * ((nx - blob2_x) ** 2 + (ny - blob2_y) ** 2))
            d3 = 1.0 / (1.0 + 10 * ((nx - blob3_x) ** 2 + (ny - blob3_y) ** 2))
            
            # Combine influences
            total = d1 + d2 + d3
            color_pos = (d1 * 0.0 + d2 * 0.4 + d3 * 0.8) / max(total, 0.01) + phase * 0.2
            r, g, b = self._interpolate_palette_color(palette, color_pos % 1.0)
            
            brightness = min(1.0, total * 1.5)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_breathing(self, fixtures: list, effect: EffectParameters, phase: float):
        """Gentle breathing/pulsing through a color palette."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'pastel')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['pastel'])
        
        # Smooth breathing curve
        breath = (1 - math.cos(phase * 2 * math.pi)) / 2
        breath_intensity = 0.4 + 0.6 * breath
        
        # Color slowly shifts through palette
        color_pos = phase * 0.5 % 1.0
        r, g, b = self._interpolate_palette_color(palette, color_pos)
        
        for pixel in all_pixels:
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * breath_intensity)
    
    def _apply_geo_ocean_waves(self, fixtures: list, effect: EffectParameters, phase: float):
        """Ocean waves with depth-based color gradient."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ocean']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Multiple wave layers
            wave1 = math.sin((nx * 4 + phase * 2) * math.pi) * 0.15
            wave2 = math.sin((nx * 6 - phase * 1.3) * math.pi) * 0.1
            wave3 = math.sin((nx * 2 + phase * 0.8) * math.pi) * 0.2
            
            # Combine for surface motion
            surface = 0.3 + wave1 + wave2 + wave3
            
            # Depth-based color (deeper = darker blue)
            depth = ny
            color_pos = (depth * 0.7 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Brightness based on wave height
            brightness = max(0.5, min(1.0, 0.8 + (surface - ny) * 2))
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_sunset(self, fixtures: list, effect: EffectParameters, phase: float):
        """Beautiful sunset gradient that slowly shifts."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['sunset']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Vertical gradient with slow horizontal drift
            drift = math.sin(phase * 2 * math.pi) * 0.1
            color_pos = (ny * 0.8 + drift + phase * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Slight glow effect at horizon
            horizon_glow = 1.0 + 0.3 * math.exp(-((ny - 0.7) ** 2) * 20)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * min(1.0, horizon_glow))
    
    def _apply_geo_fire_gradient(self, fixtures: list, effect: EffectParameters, phase: float):
        """Flickering fire with gradient colors."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        import random
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['fire']
        
        # Use deterministic noise based on phase for consistency
        seed = int(phase * 1000) % 10000
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Fire rises from bottom
            base_intensity = 1.0 - ny
            
            # Flickering
            flicker = math.sin(phase * 20 + nx * 10 + i * 0.5) * 0.2
            flicker += math.sin(phase * 35 + nx * 15) * 0.1
            
            # Color based on height (hotter/whiter at bottom)
            color_pos = (ny * 0.7 + phase * 0.3) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = max(0.1, min(1.0, base_intensity + flicker))
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_galaxy(self, fixtures: list, effect: EffectParameters, phase: float):
        """Swirling galaxy with purple/blue palette."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['galaxy']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Convert to polar from center
            cx, cy = nx - 0.5, ny - 0.5
            dist = (cx ** 2 + cy ** 2) ** 0.5
            angle = math.atan2(cy, cx)
            
            # Spiral arms
            spiral = (angle / (2 * math.pi) + dist * 2 - phase) % 1.0
            arm_intensity = (math.sin(spiral * 4 * math.pi) + 1) / 2
            
            # Core glow
            core_glow = math.exp(-dist * 5)
            
            color_pos = (spiral + phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = max(0.1, min(1.0, arm_intensity * 0.7 + core_glow * 0.5))
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_rainbow_flow(self, fixtures: list, effect: EffectParameters, phase: float):
        """Smooth flowing rainbow gradient."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['rainbow']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            color_pos = (nx + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
    
    def _apply_geo_neon_pulse(self, fixtures: list, effect: EffectParameters, phase: float):
        """Pulsing neon colors."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['neon']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Create pulsing zones
            zone = int(nx * 5) % 5
            zone_phase = (phase + zone * 0.2) % 1.0
            pulse = (1 - math.cos(zone_phase * 2 * math.pi)) / 2
            
            color_pos = (zone / 5 + phase * 0.3) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.3 + 0.7 * pulse
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_tropical(self, fixtures: list, effect: EffectParameters, phase: float):
        """Tropical/warm palette flow."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['tropical']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Gentle wave motion
            wave = math.sin((nx * 2 + phase) * math.pi) * 0.1
            color_pos = (nx * 0.5 + ny * 0.3 + wave + phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
    
    # ==================== SLOW AMBIENT & ARTISTIC EFFECTS ====================
    
    def _apply_geo_silk(self, fixtures: list, effect: EffectParameters, phase: float):
        """Flowing silk fabric - smooth undulating waves of color."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'pastel')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['pastel'])
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Multiple slow sine waves create fabric-like undulation
            wave1 = math.sin((nx * 1.5 + phase * 0.4) * math.pi) * 0.15
            wave2 = math.sin((ny * 2 + phase * 0.3) * math.pi) * 0.1
            wave3 = math.sin((nx + ny + phase * 0.5) * math.pi) * 0.12
            
            # Combine for smooth flowing motion
            flow = wave1 + wave2 + wave3
            color_pos = (nx * 0.3 + flow + phase * 0.15) % 1.0
            
            # Subtle brightness variation for depth
            brightness = 0.85 + 0.15 * math.sin((nx * 2 + ny + phase * 0.6) * math.pi)
            
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_tide(self, fixtures: list, effect: EffectParameters, phase: float):
        """Gentle tide - colors ebb and flow like ocean water on shore."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ocean']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Tide comes in and recedes - uses smooth ease
            tide_pos = (1 - math.cos(phase * 2 * math.pi)) / 2  # 0 to 1 smooth
            tide_line = tide_pos * 0.8 + 0.1  # Between 0.1 and 0.9
            
            # Distance from current tide line
            dist_from_tide = abs(ny - tide_line)
            
            # Color based on depth (deeper = different color)
            color_pos = (ny * 0.6 + phase * 0.08) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Foam/brightness near tide line
            foam = math.exp(-dist_from_tide * 8) * 0.3
            brightness = 0.7 + foam
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_clouds(self, fixtures: list, effect: EffectParameters, phase: float):
        """Drifting clouds - soft blobs that slowly drift across."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'pastel')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['pastel'])
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Multiple cloud layers drifting at different speeds
            cloud1 = math.sin((nx * 2 - phase * 0.3) * math.pi) * math.cos((ny * 1.5) * math.pi)
            cloud2 = math.sin((nx * 1.2 - phase * 0.2 + 0.5) * math.pi) * math.cos((ny * 2 + 0.3) * math.pi)
            cloud3 = math.sin((nx * 0.8 - phase * 0.15) * math.pi) * math.cos((ny * 1.8 + 0.7) * math.pi)
            
            # Combine cloud layers
            cloud_density = (cloud1 + cloud2 * 0.7 + cloud3 * 0.5) / 2.2
            cloud_density = max(0, cloud_density)  # Only positive values
            
            # Sky color underneath, brighter where clouds are
            color_pos = (nx * 0.2 + phase * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.5 + cloud_density * 0.5
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_mist(self, fixtures: list, effect: EffectParameters, phase: float):
        """Rolling mist/fog - ethereal slow-moving wisps."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ice']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Layered noise-like patterns moving slowly
            mist1 = math.sin((nx * 3 - phase * 0.25) * math.pi + ny * 2)
            mist2 = math.cos((ny * 2.5 + phase * 0.15) * math.pi + nx * 1.5)
            mist3 = math.sin((nx * 1.5 + ny * 2 - phase * 0.2) * math.pi)
            
            # Soft combination
            mist = (mist1 * 0.4 + mist2 * 0.35 + mist3 * 0.25 + 1) / 2
            
            color_pos = (mist * 0.5 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.6 + mist * 0.4
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_candlelight(self, fixtures: list, effect: EffectParameters, phase: float):
        """Warm candlelight - gentle flickering warm glow."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Warm candle colors
        candle_palette = [(255, 147, 41), (255, 170, 60), (255, 190, 80), (255, 160, 50), (255, 140, 35)]
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Slow organic flicker - multiple frequencies
            flicker1 = math.sin(phase * 8 + i * 0.3) * 0.08
            flicker2 = math.sin(phase * 12 + i * 0.7 + 1) * 0.05
            flicker3 = math.sin(phase * 5 + i * 0.15) * 0.1
            
            flicker = 0.8 + flicker1 + flicker2 + flicker3
            
            # Subtle color variation
            color_pos = (i * 0.1 + phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(candle_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * max(0.5, min(1.0, flicker)))
    
    def _apply_geo_moonlight(self, fixtures: list, effect: EffectParameters, phase: float):
        """Moonlight shimmer - cool silvery light with subtle movement."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Cool moonlight colors
        moon_palette = [(200, 210, 230), (180, 195, 220), (220, 225, 240), (190, 200, 225), (210, 220, 235)]
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Gentle shimmer like moonlight on water
            shimmer = math.sin((nx * 4 + phase * 0.5) * math.pi) * math.cos((ny * 3 + phase * 0.3) * math.pi)
            shimmer = shimmer * 0.15 + 0.85
            
            # Very slow color drift
            color_pos = (nx * 0.2 + ny * 0.1 + phase * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(moon_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * shimmer)
    
    def _apply_geo_ripple(self, fixtures: list, effect: EffectParameters, phase: float):
        """Slow ripples emanating from center - like a stone dropped in water."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'ocean')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['ocean'])
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Distance from center
            dist = ((nx - 0.5) ** 2 + (ny - 0.5) ** 2) ** 0.5
            
            # Expanding ripples
            ripple = math.sin((dist * 8 - phase * 2) * math.pi)
            ripple = (ripple + 1) / 2  # Normalize to 0-1
            
            # Ripples fade toward edges
            fade = max(0, 1 - dist * 1.5)
            
            color_pos = (dist + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.5 + ripple * 0.5 * fade
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_meditation(self, fixtures: list, effect: EffectParameters, phase: float):
        """Meditation - very slow, calming color transitions with breathing rhythm."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Calming colors
        calm_palette = [(147, 112, 219), (138, 43, 226), (106, 90, 205), (123, 104, 238), (148, 103, 189)]
        
        # Very slow breathing (4-7-8 pattern inspired)
        breath_cycle = phase % 1.0
        if breath_cycle < 0.21:  # Inhale
            breath = breath_cycle / 0.21
        elif breath_cycle < 0.58:  # Hold
            breath = 1.0
        else:  # Exhale
            breath = 1.0 - (breath_cycle - 0.58) / 0.42
        
        # Smooth the breath
        breath = (1 - math.cos(breath * math.pi)) / 2
        brightness = 0.4 + breath * 0.6
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Very gentle spatial variation
            color_pos = (nx * 0.15 + ny * 0.1 + phase * 0.08) % 1.0
            r, g, b = self._interpolate_palette_color(calm_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_dreamscape(self, fixtures: list, effect: EffectParameters, phase: float):
        """Dreamscape - morphing abstract shapes with soft colors."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['pastel']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Morphing blob-like shapes
            blob1 = math.sin((nx * 2 + phase * 0.3) * math.pi) * math.cos((ny * 2.5 + phase * 0.2) * math.pi)
            blob2 = math.cos((nx * 1.5 - phase * 0.25) * math.pi) * math.sin((ny * 1.8 - phase * 0.15) * math.pi)
            blob3 = math.sin((nx + ny) * 2 * math.pi + phase * 0.4)
            
            # Combine for dreamy effect
            dream = (blob1 + blob2 * 0.8 + blob3 * 0.5) / 2.3
            dream = (dream + 1) / 2  # Normalize
            
            color_pos = (dream * 0.6 + phase * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.6 + dream * 0.4
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_northern_lights(self, fixtures: list, effect: EffectParameters, phase: float):
        """Northern lights - vertical curtains of color that sway and shimmer."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Northern lights colors
        aurora_palette = [(0, 255, 127), (0, 200, 200), (100, 149, 237), (138, 43, 226), (0, 255, 200)]
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Vertical curtains that sway
            sway = math.sin(phase * 0.5 * math.pi + nx * 3) * 0.15
            curtain_x = nx + sway
            
            # Multiple curtain layers
            curtain1 = math.sin((curtain_x * 4 + phase * 0.3) * math.pi)
            curtain2 = math.sin((curtain_x * 6 - phase * 0.2) * math.pi) * 0.6
            
            # Vertical shimmer
            shimmer = math.sin((ny * 8 + phase * 2) * math.pi) * 0.1
            
            # Combine curtains
            intensity = (curtain1 + curtain2) / 2
            intensity = max(0, (intensity + 1) / 2 + shimmer)
            
            # Fade toward bottom
            v_fade = 1.0 - ny * 0.5
            
            color_pos = (curtain_x * 0.5 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(aurora_palette, color_pos)
            
            brightness = intensity * v_fade
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_waterfall(self, fixtures: list, effect: EffectParameters, phase: float):
        """Waterfall - colors cascading downward with mist."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ocean']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Falling water streams
            stream = math.sin((nx * 6 + (ny + phase) * 3) * math.pi)
            
            # Mist at bottom
            mist = math.exp(-((ny - 0.9) ** 2) * 10) * math.sin((nx * 8 + phase * 2) * math.pi) * 0.2
            
            # Combine
            water = (stream + 1) / 2 * 0.7 + abs(mist)
            
            color_pos = (ny * 0.5 + phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * water)
    
    def _apply_geo_ember(self, fixtures: list, effect: EffectParameters, phase: float):
        """Glowing embers - warm spots that pulse and fade slowly."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Ember colors - deep reds to orange
        ember_palette = [(139, 0, 0), (178, 34, 34), (255, 69, 0), (255, 99, 71), (255, 140, 0)]
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Each pixel is an ember with its own pulse cycle
            ember_phase = (phase + i * 0.13) % 1.0
            
            # Slow pulse with asymmetric rise/fall
            if ember_phase < 0.3:
                glow = ember_phase / 0.3
            else:
                glow = 1.0 - (ember_phase - 0.3) / 0.7
            
            # Smooth the glow
            glow = (1 - math.cos(glow * math.pi)) / 2
            
            # Color shifts as ember glows
            color_pos = (glow * 0.5 + i * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(ember_palette, color_pos)
            
            brightness = 0.2 + glow * 0.8
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_prism(self, fixtures: list, effect: EffectParameters, phase: float):
        """Prism - light refracting into slowly shifting rainbow bands."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['rainbow']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Diagonal bands that slowly shift
            band_pos = nx * 0.7 + ny * 0.3 - phase * 0.15
            
            # Create soft-edged bands
            band = (math.sin(band_pos * 4 * math.pi) + 1) / 2
            
            color_pos = (band_pos + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Subtle sparkle
            sparkle = 1.0 + 0.1 * math.sin((nx * 10 + ny * 10 + phase * 3) * math.pi)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * min(1.0, band * sparkle))
    
    def _apply_geo_coral(self, fixtures: list, effect: EffectParameters, phase: float):
        """Coral reef - organic shapes with tropical colors swaying gently."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Coral colors
        coral_palette = [(255, 127, 80), (255, 99, 71), (255, 160, 122), (240, 128, 128), (255, 182, 193)]
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Swaying motion like underwater
            sway = math.sin(phase * 0.4 * math.pi + ny * 2) * 0.1
            
            # Organic blob shapes
            coral1 = math.sin((nx + sway) * 4 * math.pi) * math.cos(ny * 3 * math.pi)
            coral2 = math.cos((nx - sway) * 3 * math.pi) * math.sin(ny * 4 * math.pi)
            
            shape = (coral1 + coral2 + 2) / 4
            
            color_pos = (shape * 0.5 + phase * 0.08) % 1.0
            r, g, b = self._interpolate_palette_color(coral_palette, color_pos)
            
            brightness = 0.5 + shape * 0.5
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_bioluminescence(self, fixtures: list, effect: EffectParameters, phase: float):
        """Bioluminescence - glowing spots that appear and fade like deep sea creatures."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Deep sea bioluminescent colors
        bio_palette = [(0, 255, 255), (0, 191, 255), (64, 224, 208), (127, 255, 212), (0, 206, 209)]
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Multiple glowing spots with different phases
            glow1_phase = (phase * 0.3 + i * 0.17) % 1.0
            glow2_phase = (phase * 0.25 + i * 0.23 + 0.5) % 1.0
            
            # Smooth glow curves
            glow1 = max(0, math.sin(glow1_phase * math.pi) ** 3)
            glow2 = max(0, math.sin(glow2_phase * math.pi) ** 3) * 0.5
            
            glow = min(1.0, glow1 + glow2)
            
            # Base deep blue with glowing spots
            if glow > 0.1:
                color_pos = (i * 0.1 + phase * 0.15) % 1.0
                r, g, b = self._interpolate_palette_color(bio_palette, color_pos)
            else:
                r, g, b = 0, 20, 40  # Deep sea darkness
            
            brightness = 0.1 + glow * 0.9
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_zen(self, fixtures: list, effect: EffectParameters, phase: float):
        """Zen garden - minimal, calming, very slow transitions."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Zen colors - muted, natural
        zen_palette = [(169, 169, 169), (188, 184, 177), (210, 206, 200), (190, 180, 165), (175, 170, 160)]
        
        # Very slow color drift - almost imperceptible
        base_color_pos = phase * 0.05
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Minimal variation - just subtle gradients
            color_pos = (base_color_pos + nx * 0.1 + ny * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(zen_palette, color_pos)
            
            # Very subtle brightness wave
            wave = math.sin((nx + ny + phase * 0.3) * math.pi) * 0.05
            brightness = 0.9 + wave
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    # ==================== RANDOM FADE & DIMMING EFFECTS ====================
    
    def _apply_geo_random_fade(self, fixtures: list, effect: EffectParameters, phase: float):
        """Random pixels smoothly fade in and out at different times."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'pastel')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['pastel'])
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Each pixel has its own fade cycle offset based on position
            # Use golden ratio for nice distribution
            offset = (i * 0.618033988749895) % 1.0
            pixel_phase = (phase + offset) % 1.0
            
            # Smooth fade curve - slow in, slow out
            fade = (1 - math.cos(pixel_phase * 2 * math.pi)) / 2
            
            color_pos = (i * 0.07 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * fade)
    
    def _apply_geo_breathing_wave(self, fixtures: list, effect: EffectParameters, phase: float):
        """Wave of dimming that travels across - fixtures fade as wave passes."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'ocean')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['ocean'])
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Wave position travels across
            wave_pos = (phase * 2) % 2.0  # 0 to 2
            if wave_pos > 1.0:
                wave_pos = 2.0 - wave_pos  # Bounce back
            
            # Distance from wave front
            dist = abs(nx - wave_pos)
            
            # Smooth gaussian-like falloff
            brightness = math.exp(-dist * dist * 8)
            
            color_pos = (nx * 0.5 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_twinkle_fade(self, fixtures: list, effect: EffectParameters, phase: float):
        """Gentle twinkling - random pixels softly brighten and dim like stars."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'pastel')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['pastel'])
        
        for i, pixel in enumerate(all_pixels):
            # Multiple overlapping sine waves for organic feel
            t1 = math.sin((phase * 3 + i * 0.37) * math.pi) * 0.3
            t2 = math.sin((phase * 2.3 + i * 0.53) * math.pi) * 0.25
            t3 = math.sin((phase * 1.7 + i * 0.71) * math.pi) * 0.2
            
            # Combine for twinkle effect, always positive
            twinkle = 0.25 + max(0, t1 + t2 + t3)
            twinkle = min(1.0, twinkle)
            
            color_pos = (i * 0.08 + phase * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * twinkle)
    
    def _apply_geo_spotlight_wander(self, fixtures: list, effect: EffectParameters, phase: float):
        """Soft spotlight that slowly wanders across the canvas."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'sunset')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['sunset'])
        
        # Spotlight slowly moves in a figure-8 pattern
        spot_x = 0.5 + 0.35 * math.sin(phase * 2 * math.pi)
        spot_y = 0.5 + 0.25 * math.sin(phase * 4 * math.pi)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Distance from spotlight center
            dist = ((nx - spot_x) ** 2 + (ny - spot_y) ** 2) ** 0.5
            
            # Soft falloff - gaussian
            brightness = math.exp(-dist * dist * 6)
            
            # Ambient glow so nothing is completely dark
            brightness = 0.1 + brightness * 0.9
            
            color_pos = (dist + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_cascade_dim(self, fixtures: list, effect: EffectParameters, phase: float):
        """Cascading dimming - pixels fade out in sequence then fade back in."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'aurora')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['aurora'])
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Cascade based on position (diagonal)
            cascade_pos = (nx + ny) / 2
            pixel_phase = (phase + cascade_pos * 0.5) % 1.0
            
            # Smooth fade cycle
            if pixel_phase < 0.5:
                brightness = 1.0 - (pixel_phase * 2)  # Fade out
            else:
                brightness = (pixel_phase - 0.5) * 2  # Fade in
            
            # Smooth the transition
            brightness = (1 - math.cos(brightness * math.pi)) / 2
            
            color_pos = (cascade_pos + phase * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_firefly(self, fixtures: list, effect: EffectParameters, phase: float):
        """Fireflies - random pixels glow softly then fade, like fireflies in a field."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Warm yellow-green firefly colors
        firefly_palette = [(144, 238, 144), (173, 255, 47), (154, 205, 50), (127, 255, 0), (200, 255, 100)]
        
        for i, pixel in enumerate(all_pixels):
            # Each firefly has its own random-ish timing
            offset = (i * 0.618033988749895 + i * i * 0.01) % 1.0
            fly_phase = (phase * 0.5 + offset) % 1.0
            
            # Firefly glow pattern - quick brighten, slow fade
            if fly_phase < 0.15:
                glow = fly_phase / 0.15  # Quick rise
            elif fly_phase < 0.5:
                glow = 1.0 - (fly_phase - 0.15) / 0.35  # Slow fade
            else:
                glow = 0  # Dark period
            
            # Smooth the glow
            glow = glow ** 0.5 if glow > 0 else 0
            
            color_pos = (i * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(firefly_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * glow)
    
    def _apply_geo_rolling_blackout(self, fixtures: list, effect: EffectParameters, phase: float):
        """Rolling blackout - smooth darkness rolls across then retreats."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'sunset')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['sunset'])
        
        # Shadow position oscillates
        shadow_pos = math.sin(phase * math.pi) * 0.6 + 0.5
        shadow_width = 0.3
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Distance from shadow center
            dist = abs(nx - shadow_pos)
            
            # Shadow creates dimming
            if dist < shadow_width:
                dim = 1.0 - (1.0 - dist / shadow_width) * 0.8
            else:
                dim = 1.0
            
            # Smooth the edges
            dim = (dim + 1) / 2 if dim < 0.5 else dim
            
            color_pos = (nx * 0.5 + phase * 0.08) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * dim)
    
    def _apply_geo_heartbeat_dim(self, fixtures: list, effect: EffectParameters, phase: float):
        """Heartbeat dimming - all pixels pulse together with heartbeat rhythm."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette_name = getattr(effect, 'palette', 'candy')
        palette = self.GRADIENT_PALETTES.get(palette_name, self.GRADIENT_PALETTES['candy'])
        
        # Heartbeat pattern - two beats then pause
        beat_phase = phase % 1.0
        if beat_phase < 0.15:
            # First beat rise
            pulse = beat_phase / 0.15
        elif beat_phase < 0.25:
            # First beat fall
            pulse = 1.0 - (beat_phase - 0.15) / 0.1
        elif beat_phase < 0.35:
            # Second beat rise
            pulse = (beat_phase - 0.25) / 0.1 * 0.7
        elif beat_phase < 0.45:
            # Second beat fall
            pulse = 0.7 * (1.0 - (beat_phase - 0.35) / 0.1)
        else:
            # Rest
            pulse = 0
        
        # Smooth the pulse
        pulse = (1 - math.cos(pulse * math.pi)) / 2
        brightness = 0.3 + pulse * 0.7
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            color_pos = (nx * 0.3 + ny * 0.2 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_rain_fade(self, fixtures: list, effect: EffectParameters, phase: float):
        """Rain fade - droplets of dimming fall down the canvas."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ocean']
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Multiple rain columns at different speeds
            col1 = math.sin((nx * 8 + i * 0.1) * math.pi) > 0.5
            col2 = math.sin((nx * 12 + i * 0.2 + 0.5) * math.pi) > 0.6
            col3 = math.sin((nx * 6 + i * 0.15 + 0.3) * math.pi) > 0.55
            
            brightness = 0.4
            
            # Raindrops falling in columns
            if col1:
                drop1 = ((phase * 1.5 - ny) % 1.0)
                if drop1 < 0.2:
                    brightness += (1 - drop1 / 0.2) * 0.3
            
            if col2:
                drop2 = ((phase * 1.2 - ny + 0.3) % 1.0)
                if drop2 < 0.15:
                    brightness += (1 - drop2 / 0.15) * 0.25
            
            if col3:
                drop3 = ((phase * 0.9 - ny + 0.6) % 1.0)
                if drop3 < 0.18:
                    brightness += (1 - drop3 / 0.18) * 0.2
            
            brightness = min(1.0, brightness)
            
            color_pos = (ny * 0.5 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_nebula(self, fixtures: list, effect: EffectParameters, phase: float):
        """Nebula - cosmic clouds with stars fading in and out."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['galaxy']
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Nebula cloud layers
            cloud1 = math.sin((nx * 3 + phase * 0.3) * math.pi) * math.cos((ny * 2.5 + phase * 0.2) * math.pi)
            cloud2 = math.cos((nx * 2 - phase * 0.25) * math.pi) * math.sin((ny * 3 - phase * 0.15) * math.pi)
            
            nebula = (cloud1 + cloud2 + 2) / 4
            
            # Random stars twinkling
            star_offset = (i * 0.618033988749895) % 1.0
            star_twinkle = math.sin((phase * 2 + star_offset * 10) * math.pi)
            is_star = (i * 7 + i * i) % 13 < 2  # ~15% are stars
            
            if is_star and star_twinkle > 0.3:
                brightness = nebula * 0.5 + star_twinkle * 0.5
            else:
                brightness = nebula * 0.7
            
            color_pos = (nebula * 0.5 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_lanterns(self, fixtures: list, effect: EffectParameters, phase: float):
        """Floating lanterns - warm glows that drift and flicker gently."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Warm lantern colors
        lantern_palette = [(255, 200, 100), (255, 180, 80), (255, 160, 60), (255, 220, 120), (255, 190, 90)]
        
        # Create 5 lantern positions that drift
        lanterns = []
        for j in range(5):
            lx = 0.15 + 0.7 * ((j * 0.618) % 1.0) + 0.05 * math.sin(phase * 2 * math.pi + j)
            ly = 0.2 + 0.6 * ((j * 0.382) % 1.0) + 0.08 * math.sin(phase * 1.5 * math.pi + j * 2)
            lanterns.append((lx, ly))
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Find brightness from all lanterns
            brightness = 0.05  # Ambient
            for j, (lx, ly) in enumerate(lanterns):
                dist = ((nx - lx) ** 2 + (ny - ly) ** 2) ** 0.5
                lantern_glow = math.exp(-dist * dist * 15)
                # Gentle flicker
                flicker = 0.9 + 0.1 * math.sin(phase * 8 + j * 2)
                brightness += lantern_glow * flicker * 0.4
            
            brightness = min(1.0, brightness)
            
            color_pos = (i * 0.05 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(lantern_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_jellyfish(self, fixtures: list, effect: EffectParameters, phase: float):
        """Jellyfish - bioluminescent pulses that drift and glow."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Jellyfish colors - ethereal blues and pinks
        jelly_palette = [(255, 105, 180), (138, 43, 226), (0, 191, 255), (64, 224, 208), (255, 182, 193)]
        
        # Multiple jellyfish drifting
        jellies = []
        for j in range(4):
            jx = 0.2 + 0.6 * ((j * 0.618 + phase * 0.15) % 1.0)
            jy = 0.3 + 0.4 * math.sin(phase * 0.5 * math.pi + j) + 0.1 * j
            pulse = (math.sin((phase * 2 + j * 0.5) * math.pi) + 1) / 2
            jellies.append((jx, jy, pulse))
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            brightness = 0.05
            color_blend = 0.0
            
            for j, (jx, jy, pulse) in enumerate(jellies):
                dist = ((nx - jx) ** 2 + (ny - jy) ** 2) ** 0.5
                glow = math.exp(-dist * dist * 12) * (0.5 + pulse * 0.5)
                brightness += glow * 0.5
                color_blend += glow * j
            
            brightness = min(1.0, brightness)
            
            color_pos = (color_blend * 0.2 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(jelly_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_morning_mist(self, fixtures: list, effect: EffectParameters, phase: float):
        """Morning mist - soft light gradually revealing through fog."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Soft morning colors
        morning_palette = [(255, 218, 185), (255, 228, 196), (255, 239, 213), (250, 235, 215), (255, 245, 238)]
        
        # Mist clears from top to bottom slowly
        clear_line = phase * 1.2  # Goes beyond 1 for full clear
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Mist density based on position relative to clear line
            mist_density = max(0, min(1, (ny - clear_line + 0.3) * 3))
            
            # Swirling mist
            swirl = math.sin((nx * 4 + phase * 0.5) * math.pi) * 0.1
            mist_density += swirl * mist_density
            
            # Brightness is inverse of mist
            brightness = 1.0 - mist_density * 0.7
            
            color_pos = (nx * 0.2 + phase * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(morning_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_aurora_dim(self, fixtures: list, effect: EffectParameters, phase: float):
        """Aurora with dimming - curtains of light that fade in and out."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['aurora']
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Vertical curtains that sway
            curtain_x = nx + math.sin(phase * 0.5 * math.pi + ny * 2) * 0.1
            
            # Multiple curtain layers with different phases
            c1 = math.sin((curtain_x * 5 + phase * 0.4) * math.pi)
            c2 = math.sin((curtain_x * 7 - phase * 0.3) * math.pi) * 0.7
            c3 = math.sin((curtain_x * 3 + phase * 0.25) * math.pi) * 0.5
            
            curtain = (c1 + c2 + c3) / 2.2
            curtain = max(0, (curtain + 1) / 2)
            
            # Overall intensity fades in and out
            master_fade = (math.sin(phase * 0.3 * math.pi) + 1) / 2
            master_fade = 0.3 + master_fade * 0.7
            
            # Vertical fade (stronger at top)
            v_fade = 1.0 - ny * 0.4
            
            brightness = curtain * master_fade * v_fade
            
            color_pos = (curtain_x * 0.4 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
    
    def _apply_geo_stardust(self, fixtures: list, effect: EffectParameters, phase: float):
        """Stardust - particles of light slowly drifting and fading."""
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        # Stardust colors - silvery with hints of color
        dust_palette = [(220, 220, 255), (255, 250, 250), (230, 230, 250), (248, 248, 255), (240, 248, 255)]
        
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Each particle drifts slowly
            drift_x = (nx + phase * 0.1 + i * 0.01) % 1.0
            drift_y = (ny + phase * 0.08) % 1.0
            
            # Particle glow based on multiple sine waves
            glow1 = math.sin((drift_x * 6 + phase * 2 + i * 0.3) * math.pi)
            glow2 = math.sin((drift_y * 8 + phase * 1.5 + i * 0.5) * math.pi)
            glow3 = math.sin((phase * 3 + i * 0.7) * math.pi)
            
            glow = (glow1 * glow2 + 1) / 2 * 0.6 + max(0, glow3) * 0.4
            glow = glow ** 1.5  # Make bright spots brighter
            
            color_pos = (i * 0.06 + phase * 0.08) % 1.0
            r, g, b = self._interpolate_palette_color(dust_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * glow)
    
    # ==================== PIXEL PICTURE / POSITION PATTERN EFFECTS ====================
    
    def _apply_pixel_snake(self, fixtures: list, effect: EffectParameters, phase: float):
        """A glowing snake that slithers across the pixel canvas using fixture positions.
        
        The snake head follows a Lissajous curve and leaves a fading tail behind it.
        Pixels near the snake path light up based on their physical position.
        Sizes scale automatically based on pixel density and canvas aspect ratio.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']
        
        # Snake body: store last N positions along curving path
        num_segments = 20
        # Scale snake width to cover ~3 pixels on each side
        snake_width = max(metrics['pixel_radius'], 0.12)
        
        # Build snake body positions from parametric curve
        segments = []
        for seg in range(num_segments):
            t = phase - seg * 0.012
            seg_x = 0.5 + 0.4 * math.sin(t * 2 * math.pi * 1.3)
            seg_y = 0.5 + 0.4 * math.cos(t * 2 * math.pi * 0.7)
            segments.append((seg_x, seg_y, 1.0 - seg / num_segments))
        
        r_base, g_base, b_base = hex_to_rgb(effect.color)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            best_brightness = 0.0
            best_seg_idx = -1
            
            for seg_idx, (seg_x, seg_y, falloff) in enumerate(segments):
                dx = (nx - seg_x) * sx
                dy = (ny - seg_y) * sy
                dist = (dx * dx + dy * dy) ** 0.5
                if dist < snake_width:
                    b_val = (1.0 - dist / snake_width) * falloff
                    if b_val > best_brightness:
                        best_brightness = b_val
                        best_seg_idx = seg_idx
            
            if best_brightness > 0:
                if best_seg_idx == 0:
                    r, g, b = 255, 255, 255
                elif best_seg_idx < 3:
                    r, g, b = r_base, g_base, b_base
                else:
                    fade = best_seg_idx / num_segments
                    r = int(r_base * (1.0 - fade * 0.6))
                    g = int(g_base * (1.0 - fade * 0.6))
                    b = int(b_base * (1.0 - fade * 0.6))
                self._apply_color_to_pixel(pixel, r, g, b, best_brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_pixel_rain_drops(self, fixtures: list, effect: EffectParameters, phase: float):
        """Rain drops fall from top to bottom, creating expanding ripples where they land.
        
        Uses fixture Y position to simulate gravity; ripples expand outward from
        impact points at the bottom.  All sizes scale to pixel density.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']
        pr = metrics['pixel_radius']
        r_base, g_base, b_base = hex_to_rgb(effect.color)
        
        num_drops = 5
        drop_width = max(pr, 0.06)
        ring_width = max(pr * 0.8, 0.05)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            total_brightness = 0.0
            
            for d in range(num_drops):
                drop_phase = (phase * 1.5 + d * 0.2) % 1.0
                drop_x = (0.15 + d * 0.18) % 1.0
                
                if drop_phase < 0.5:
                    drop_y = drop_phase * 2.0
                    dx = (nx - drop_x) * sx
                    dy = (ny - drop_y) * sy
                    dist = (dx * dx + dy * dy) ** 0.5
                    if dist < drop_width:
                        total_brightness += (1.0 - dist / drop_width)
                else:
                    ripple_age = (drop_phase - 0.5) * 2.0
                    ripple_radius = ripple_age * 0.4
                    dx = (nx - drop_x) * sx
                    dy = (ny - 1.0) * sy
                    dist = (dx * dx + dy * dy) ** 0.5
                    ring_dist = abs(dist - ripple_radius)
                    if ring_dist < ring_width:
                        ring_brightness = (1.0 - ring_dist / ring_width) * (1.0 - ripple_age)
                        total_brightness += ring_brightness
            
            total_brightness = min(1.0, total_brightness)
            if total_brightness > 0.01:
                r = min(255, int(r_base * 0.5 + 100 * total_brightness))
                g = min(255, int(g_base * 0.5 + 130 * total_brightness))
                b = min(255, int(b_base * 0.5 + 200 * total_brightness))
                self._apply_color_to_pixel(pixel, r, g, b, total_brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_pixel_sine_wave(self, fixtures: list, effect: EffectParameters, phase: float):
        """A thick colored sine wave scrolls horizontally across the pixel canvas.
        
        The wave amplitude and frequency create a flowing ribbon effect.
        Wave thickness scales to pixel density.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sy = metrics['scale_y']
        # Wave thickness in scaled-Y space — cover several pixels
        wave_thickness = max(metrics['pixel_radius'] * 1.5, 0.12) / sy if sy > 0.001 else 0.2
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            wave_y = 0.5 + 0.35 * math.sin((nx * 3 - phase * 2) * math.pi)
            wave_y += 0.1 * math.sin((nx * 7 + phase * 3) * math.pi)
            
            dist = abs(ny - wave_y)
            
            if dist < wave_thickness:
                brightness = 1.0 - (dist / wave_thickness)
                brightness = brightness ** 0.7
                
                if getattr(effect, 'rainbow_colors', False):
                    hue = (nx + phase) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = hex_to_rgb(effect.color)
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_pixel_clock(self, fixtures: list, effect: EffectParameters, phase: float):
        """A sweeping clock hand rotates around the center of the pixel canvas.
        
        Draws a bright radial line from center, plus a fading trail behind it.
        All radii and widths scale to canvas metrics.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']
        pr = metrics['pixel_radius']
        r_base, g_base, b_base = hex_to_rgb(effect.color)
        
        cx, cy = 0.5, 0.5
        hand_angle = phase * 2 * math.pi
        hand_angular_width = max(0.08, pr * 1.5)  # radians
        trail_length = math.pi * 0.5
        # Scale radii so clock fills the canvas
        face_outer = 0.48
        face_inner = 0.36
        center_dot = max(pr, 0.03)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            dx = (nx - cx) * sx
            dy = (ny - cy) * sy
            dist = (dx * dx + dy * dy) ** 0.5
            
            if dist < center_dot:
                self._apply_color_to_pixel(pixel, 255, 255, 255, 0.8 * intensity_scale)
                continue
            
            pixel_angle = math.atan2(dy, dx)
            angle_diff = (pixel_angle - hand_angle) % (2 * math.pi)
            if angle_diff > math.pi:
                angle_diff -= 2 * math.pi
            
            brightness = 0.0
            
            # Clock face ring
            if face_inner < dist < face_outer:
                brightness = max(brightness, 0.15)
            
            # Hour markers
            marker_zone = max(pr, 0.03)
            for h in range(12):
                marker_angle = h * math.pi / 6
                m_diff = abs(((pixel_angle - marker_angle + math.pi) % (2 * math.pi)) - math.pi)
                if m_diff < marker_zone and face_inner - 0.02 < dist < face_outer + 0.02:
                    brightness = max(brightness, 0.4)
            
            # Clock hand
            if abs(angle_diff) < hand_angular_width and dist < face_outer:
                hand_brightness = 1.0 - abs(angle_diff) / hand_angular_width
                brightness = max(brightness, hand_brightness)
            
            # Trail behind hand
            trail_angle = (-angle_diff) % (2 * math.pi)
            if trail_angle < trail_length and dist < face_inner + 0.04:
                trail_brightness = (1.0 - trail_angle / trail_length) * 0.5
                brightness = max(brightness, trail_brightness)
            
            if brightness > 0.01:
                self._apply_color_to_pixel(pixel, r_base, g_base, b_base, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_pixel_orbits(self, fixtures: list, effect: EffectParameters, phase: float):
        """Multiple colored orbs orbit around a central point at different speeds and radii.
        
        Orb sizes scale to pixel density so they always light up multiple pixels.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']
        pr = metrics['pixel_radius']
        
        cx, cy = 0.5, 0.5
        orb_size = max(pr * 1.2, 0.08)
        center_glow = max(pr, 0.06)
        ring_width = max(pr * 0.5, 0.02)
        
        orbs = [
            (0.12, 3.0, 0.05),
            (0.22, 2.0, 0.3),
            (0.32, 1.0, 0.6),
            (0.42, 0.6, 0.85),
        ]
        
        r_base, g_base, b_base = hex_to_rgb(effect.color)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            best_brightness = 0.0
            best_r, best_g, best_b = 0, 0, 0
            
            # Center glow
            dx = (nx - cx) * sx
            dy = (ny - cy) * sy
            center_dist = (dx * dx + dy * dy) ** 0.5
            if center_dist < center_glow:
                best_brightness = 1.0 - center_dist / center_glow
                best_r, best_g, best_b = 255, 200, 80
            
            for radius, speed, hue in orbs:
                angle = phase * speed * 2 * math.pi
                orb_x = cx + radius * math.cos(angle) / sx if sx > 0.001 else cx
                orb_y = cy + radius * math.sin(angle) / sy if sy > 0.001 else cy
                
                odx = (nx - orb_x) * sx
                ody = (ny - orb_y) * sy
                dist = (odx * odx + ody * ody) ** 0.5
                if dist < orb_size:
                    b_val = (1.0 - dist / orb_size) ** 0.6
                    if b_val > best_brightness:
                        best_brightness = b_val
                        if getattr(effect, 'rainbow_colors', False):
                            color = get_rainbow_color(hue)
                            best_r, best_g, best_b = hex_to_rgb(color)
                        else:
                            best_r, best_g, best_b = r_base, g_base, b_base
                
                # Orbit ring
                orbit_dist = abs(center_dist - radius)
                if orbit_dist < ring_width and best_brightness < 0.1:
                    best_brightness = max(best_brightness, 0.1)
                    best_r = max(best_r, 40)
                    best_g = max(best_g, 40)
                    best_b = max(best_b, 60)
            
            if best_brightness > 0.01:
                self._apply_color_to_pixel(pixel, best_r, best_g, best_b, best_brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_pixel_starfield(self, fixtures: list, effect: EffectParameters, phase: float):
        """Stars rush outward from center creating a warp-speed starfield effect.
        
        Streak sizes scale to pixel density.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']
        pr = metrics['pixel_radius']
        
        cx, cy = 0.5, 0.5
        num_stars = 16
        base_streak_w = max(pr * 0.8, 0.03)
        base_streak_l = max(pr * 1.5, 0.05)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            pdx = (nx - cx) * sx
            pdy = (ny - cy) * sy
            pixel_dist = (pdx * pdx + pdy * pdy) ** 0.5
            pixel_angle = math.atan2(pdy, pdx)
            
            total_brightness = 0.0
            
            for s in range(num_stars):
                star_angle = (s * 2 * math.pi / num_stars) + s * 0.3
                star_phase = (phase * 2 + s * (1.0 / num_stars)) % 1.0
                
                star_dist = star_phase ** 1.5 * 0.7
                
                streak_width = base_streak_w + star_phase * base_streak_w
                streak_length = base_streak_l + star_phase * base_streak_l * 2
                
                angle_diff = abs(((pixel_angle - star_angle + math.pi) % (2 * math.pi)) - math.pi)
                
                if angle_diff < 0.3:
                    radial_diff = abs(pixel_dist - star_dist)
                    if radial_diff < streak_length:
                        lateral = angle_diff * pixel_dist
                        if lateral < streak_width:
                            b_val = (1.0 - radial_diff / streak_length) * (1.0 - lateral / streak_width)
                            b_val *= star_phase
                            total_brightness += b_val
            
            total_brightness = min(1.0, total_brightness)
            if total_brightness > 0.01:
                r = int(200 + 55 * total_brightness)
                g = int(200 + 55 * total_brightness)
                b = 255
                self._apply_color_to_pixel(pixel, r, g, b, total_brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_pixel_diamond(self, fixtures: list, effect: EffectParameters, phase: float):
        """A rotating diamond shape that pulses and shifts across the canvas.
        
        Diamond size scales to canvas metrics so it always covers many pixels.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']
        pr = metrics['pixel_radius']
        r_base, g_base, b_base = hex_to_rgb(effect.color)
        
        t = phase * 2 * math.pi
        dcx = 0.5 + 0.2 * math.sin(t)
        dcy = 0.5 + 0.15 * math.sin(t * 2)
        
        rotation = phase * math.pi
        diamond_size = 0.22 + 0.06 * math.sin(phase * 4 * math.pi)
        edge_width = max(pr * 0.8, 0.03)
        
        cos_r = math.cos(rotation)
        sin_r = math.sin(rotation)
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Scale then rotate
            dx = (nx - dcx) * sx
            dy = (ny - dcy) * sy
            local_x = dx * cos_r + dy * sin_r
            local_y = -dx * sin_r + dy * cos_r
            
            diamond_dist = abs(local_x) + abs(local_y)
            
            if diamond_dist < diamond_size:
                edge_proximity = 1.0 - diamond_dist / diamond_size
                
                if edge_proximity < edge_width / diamond_size:
                    brightness = 1.0
                    r, g, b = 255, 255, 255
                else:
                    brightness = 0.4 + 0.6 * edge_proximity
                    r, g, b = r_base, g_base, b_base
                
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_pixel_butterfly(self, fixtures: list, effect: EffectParameters, phase: float):
        """Butterfly wing pattern that gently flaps open and closed.
        
        Wing thickness and body width scale to pixel density.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']
        pr = metrics['pixel_radius']
        
        cx, cy = 0.5, 0.5
        flap = 0.6 + 0.4 * math.sin(phase * 2 * math.pi)
        wing_thickness = max(pr * 1.5, 0.10)
        body_width = max(pr, 0.03)
        center_dot = max(pr * 0.5, 0.015)
        
        wing_palette = [
            (255, 120, 0), (255, 50, 150), (180, 0, 255),
            (50, 100, 255), (0, 200, 180),
        ]
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            dx = (nx - cx) * sx
            dy = (ny - cy) * sy
            dist = (dx * dx + dy * dy) ** 0.5
            angle = math.atan2(dy, dx)
            
            if dist < center_dot:
                self._apply_color_to_pixel(pixel, 200, 200, 200, 0.8 * intensity_scale)
                continue
            
            wing_r = abs(math.sin(2 * angle)) * 0.4 * flap
            wing_dist = abs(dist - wing_r)
            
            if wing_dist < wing_thickness and dist < 0.55:
                brightness = (1.0 - wing_dist / wing_thickness)
                color_pos = (dist / 0.4 + phase * 0.3) % 1.0
                r, g, b = self._interpolate_palette_color(wing_palette, color_pos)
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            elif abs(dx) < body_width and abs(dy) < 0.25:
                self._apply_color_to_pixel(pixel, 180, 150, 100, 0.6 * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_pixel_spinner(self, fixtures: list, effect: EffectParameters, phase: float):
        """Multi-armed spinner that rotates around center.
        
        Arm blob sizes and connector widths scale to pixel density.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']
        pr = metrics['pixel_radius']
        r_base, g_base, b_base = hex_to_rgb(effect.color)
        
        cx, cy = 0.5, 0.5
        num_arms = 3
        arm_radius = 0.38
        arm_blob_size = max(pr * 1.5, 0.10)
        center_size = max(pr * 1.2, 0.08)
        arm_width = max(pr, 0.05)
        
        rotation = phase * 2 * math.pi
        if effect.direction == 'backward':
            rotation = -rotation
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            dx = (nx - cx) * sx
            dy = (ny - cy) * sy
            dist = (dx * dx + dy * dy) ** 0.5
            pixel_angle = math.atan2(dy, dx)
            
            best_brightness = 0.0
            best_arm = -1
            
            if dist < center_size:
                best_brightness = 1.0 - dist / center_size
                best_arm = -1
            
            for arm in range(num_arms):
                arm_angle = rotation + arm * 2 * math.pi / num_arms
                
                tip_x = arm_radius * math.cos(arm_angle)
                tip_y = arm_radius * math.sin(arm_angle)
                bdx = dx - tip_x
                bdy = dy - tip_y
                blob_dist = (bdx * bdx + bdy * bdy) ** 0.5
                
                if blob_dist < arm_blob_size:
                    b_val = 1.0 - blob_dist / arm_blob_size
                    if b_val > best_brightness:
                        best_brightness = b_val
                        best_arm = arm
                
                angle_diff = abs(((pixel_angle - arm_angle + math.pi) % (2 * math.pi)) - math.pi)
                lateral_dist = dist * math.sin(angle_diff)
                along_arm = dist * math.cos(angle_diff)
                
                if lateral_dist < arm_width and 0 < along_arm < arm_radius and angle_diff < math.pi / 2:
                    b_val = (1.0 - lateral_dist / arm_width) * 0.7
                    if b_val > best_brightness:
                        best_brightness = b_val
                        best_arm = arm
            
            if best_brightness > 0.01:
                if getattr(effect, 'rainbow_colors', False) and best_arm >= 0:
                    hue = (best_arm / num_arms + phase * 0.2) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r, g, b = r_base, g_base, b_base
                self._apply_color_to_pixel(pixel, r, g, b, best_brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)
    
    def _apply_pixel_ripple_pool(self, fixtures: list, effect: EffectParameters, phase: float):
        """Multiple ripples emanate from different points and interfere.
        
        Wave frequencies scale to canvas size so ripples are always visible.
        """
        all_pixels, bounds = self._get_unified_pixel_canvas(fixtures)
        if not all_pixels:
            self._geo_fallback_static(fixtures, effect)
            return
        
        import math
        intensity_scale = self._get_effective_intensity_scale(effect)
        metrics = self._get_pixel_canvas_metrics(all_pixels, bounds)
        sx, sy = metrics['scale_x'], metrics['scale_y']
        r_base, g_base, b_base = hex_to_rgb(effect.color)
        
        # Scale wave frequency so there are always ~3-5 visible wave crests
        # across the canvas diagonal
        diag = (sx * sx + sy * sy) ** 0.5
        base_freq = max(4.0, 6.0 / diag) if diag > 0.01 else 6.0
        
        sources = []
        num_sources = 4
        for s in range(num_sources):
            src_x = 0.5 + 0.3 * math.sin(phase * 0.7 + s * 1.57)
            src_y = 0.5 + 0.3 * math.cos(phase * 0.5 + s * 2.1)
            freq = base_freq + s * (base_freq * 0.3)
            sources.append((src_x, src_y, freq))
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            wave_sum = 0.0
            for src_x, src_y, freq in sources:
                dx = (nx - src_x) * sx
                dy = (ny - src_y) * sy
                dist = (dx * dx + dy * dy) ** 0.5
                wave = math.sin((dist * freq - phase * 4) * math.pi)
                wave_sum += wave
            
            normalized = (wave_sum / num_sources + 1.0) / 2.0
            brightness = normalized ** 1.5
            
            if brightness > 0.05:
                if getattr(effect, 'rainbow_colors', False):
                    hue = (normalized + phase * 0.3) % 1.0
                    color = get_rainbow_color(hue)
                    r, g, b = hex_to_rgb(color)
                else:
                    r = int(r_base * (0.3 + 0.7 * brightness))
                    g = int(g_base * (0.3 + 0.7 * brightness))
                    b = int(b_base * (0.3 + 0.7 * brightness))
                self._apply_color_to_pixel(pixel, r, g, b, brightness * intensity_scale)
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)

    # ==================== UNIFIED ENSEMBLE EFFECTS (All fixtures coordinated) ====================
    
    def _categorize_fixtures(self, fixtures: list) -> dict:
        """Categorize fixtures by type for coordinated effects."""
        categories = {
            'movers': [],      # Moving heads with pan/tilt
            'pixels': [],      # Pixel-mapped fixtures (LED bars, strobes with pixel tables)
            'wash': [],        # Wash/par fixtures
            'strobe': [],      # Strobes/blinders (non-pixel mapped)
            'other': []        # Other fixtures
        }
        
        for fixture in fixtures:
            if not fixture or not fixture.profile:
                continue
            
            # Get mode object properly
            mode = fixture.profile.get_mode(fixture.mode_name) if fixture.profile else None
            if not mode:
                continue
            
            # Check for pan/tilt (mover)
            has_pan_tilt = any(ch.type.lower() in ('pan', 'tilt') 
                              for ch in mode.channels)
            
            # Check for pixels - improved detection
            # Check is_pixel_fixture flag, pixel_count, pixel_layout, or pixel_channel_table
            has_pixels = (
                getattr(fixture.profile, 'is_pixel_fixture', False) or
                getattr(fixture, 'pixel_count', 0) > 1 or
                getattr(fixture, 'pixel_layout', None) is not None or
                (hasattr(fixture.profile, 'pixel_channel_table') and 
                 fixture.profile.pixel_channel_table and 
                 len(fixture.profile.pixel_channel_table) > 1)
            )
            
            category = fixture.profile.category.lower() if fixture.profile else ''
            
            if has_pan_tilt:
                categories['movers'].append(fixture)
            elif has_pixels:
                categories['pixels'].append(fixture)
            elif 'strobe' in category or 'blinder' in category:
                categories['strobe'].append(fixture)
            elif 'wash' in category or 'par' in category:
                categories['wash'].append(fixture)
            else:
                categories['other'].append(fixture)
        
        return categories
    
    def _apply_mover_position(self, fixture, pan_angle: float, tilt_angle: float, 
                               r: int, g: int, b: int, intensity: float,
                               fixture_index: int = 0, phase_offset: float = 0.0):
        """Apply pan/tilt and color to a mover fixture.
        
        Args:
            fixture: The fixture to control
            pan_angle: Pan angle in degrees from center
            tilt_angle: Tilt angle in degrees from center
            r, g, b: RGB color values 0-255
            intensity: Brightness 0.0-1.0
            fixture_index: Index of this fixture (for offsets)
            phase_offset: Additional phase offset for flowy movement timing
        
        Note: If position preview is active, pan/tilt will be skipped but color/intensity
        will still be applied.
        """
        if not fixture or not fixture.profile:
            return
        
        # Check if position preview is active - if so, skip pan/tilt but still apply color
        preview_active = self._is_preview_active()
        
        # Get mode object properly
        mode = fixture.profile.get_mode(fixture.mode_name) if fixture.profile else None
        if not mode:
            return
        
        # Apply slight phase offset to pan/tilt for flowy feel
        # Uses golden ratio based offset for visually pleasing stagger
        import math
        flow_offset = fixture_index * 0.1618 + phase_offset
        pan_flow = math.sin(flow_offset * math.pi * 2) * 5  # ±5° flow
        tilt_flow = math.cos(flow_offset * math.pi * 2) * 3  # ±3° flow
        
        pan_angle += pan_flow
        tilt_angle += tilt_flow
        
        # Get fixture calibration
        pan_range = getattr(fixture, 'pan_range', 540.0)
        tilt_range = getattr(fixture, 'tilt_range', 270.0)
        pan_offset = getattr(fixture, 'pan_offset', 0.0)
        tilt_offset = getattr(fixture, 'tilt_offset', 0.0)
        pan_invert = getattr(fixture, 'pan_invert', False)
        tilt_invert = getattr(fixture, 'tilt_invert', False)
        
        # Convert angle to DMX value
        # pan_angle is in degrees from center (-pan_range/2 to +pan_range/2)
        pan_normalized = (pan_angle - pan_offset) / pan_range + 0.5
        if pan_invert:
            pan_normalized = 1.0 - pan_normalized
        pan_dmx = int(max(0, min(255, pan_normalized * 255)))
        
        tilt_normalized = (tilt_angle - tilt_offset) / tilt_range + 0.5
        if tilt_invert:
            tilt_normalized = 1.0 - tilt_normalized
        tilt_dmx = int(max(0, min(255, tilt_normalized * 255)))
        
        # Get universe object
        uni = self.artnet.get_universe(fixture.universe)
        if not uni:
            return

        # HTP buffer-capture redirect (set by _buffer_ensemble_adapter).  When
        # active on this thread, writes go to the effect's DMX buffer for HTP
        # merging instead of straight to Art-Net.  Inactive elsewhere.
        _cap_tls = getattr(self, '_buffer_capture_tls', None)
        _cap_active = _cap_tls is not None and getattr(_cap_tls, 'active', False)
        _cap_buffer = _cap_tls.buffer if _cap_active else None

        def _emit(_addr, _val, _ctype):
            if _cap_active:
                _cap_buffer[(fixture.universe, _addr)] = (_val, _ctype)
            else:
                uni.set_channel(_addr, _val)

        # Check if this fixture has a color wheel (for spots)
        has_color_wheel = False
        color_wheel_channel = None
        color_wheel_value = -1
        
        for ch in mode.channels:
            if ch.type.lower() == 'color_wheel':
                has_color_wheel = True
                color_wheel_channel = ch
                break
        
        # If fixture has color wheel, map RGB to closest wheel color
        if has_color_wheel and color_wheel_channel and color_wheel_channel.color_wheel_colors:
            hex_color = f"#{r:02x}{g:02x}{b:02x}"
            color_wheel_value, matched_name = find_closest_color_wheel_value(
                hex_color, color_wheel_channel.color_wheel_colors
            )
        
        # Apply to channels - use enumerate to get channel offset
        for i, ch in enumerate(mode.channels):
            ch_type = ch.type.lower()
            addr = fixture.address + i
            
            if ch_type == 'pan':
                # Skip pan/tilt if position preview is active
                if not preview_active:
                    _emit(addr, pan_dmx, 'pan')
            elif ch_type == 'tilt':
                # Skip pan/tilt if position preview is active
                if not preview_active:
                    _emit(addr, tilt_dmx, 'tilt')
            elif ch_type == 'color_wheel':
                # Set color wheel if we found a matching value
                # Skip if overlay owns this channel
                if color_wheel_value >= 0 and not self._check_overlay_channel(fixture.universe, addr):
                    _emit(addr, color_wheel_value, 'color_wheel')
            elif ch_type == 'red':
                # Skip if overlay owns this channel
                if not self._check_overlay_channel(fixture.universe, addr):
                    if has_color_wheel and color_wheel_value >= 0:
                        _emit(addr, 0, 'red')
                    else:
                        _emit(addr, r, 'red')
            elif ch_type == 'green':
                if not self._check_overlay_channel(fixture.universe, addr):
                    if has_color_wheel and color_wheel_value >= 0:
                        _emit(addr, 0, 'green')
                    else:
                        _emit(addr, g, 'green')
            elif ch_type == 'blue':
                if not self._check_overlay_channel(fixture.universe, addr):
                    if has_color_wheel and color_wheel_value >= 0:
                        _emit(addr, 0, 'blue')
                    else:
                        _emit(addr, b, 'blue')
            elif ch_type in ('dimmer', 'intensity', 'master', 'master dimmer'):
                if not self._check_overlay_channel(fixture.universe, addr):
                    _emit(addr, int(intensity * 255), ch_type)
            elif ch_type == 'shutter':
                if not self._check_overlay_channel(fixture.universe, addr):
                    _emit(addr, 255 if intensity > 0.01 else 0, 'shutter')

    def _get_all_ensemble_pixels(self, fixtures: list) -> tuple:
        """
        Get ALL pixels from ALL fixtures for ensemble effects.
        This uses the unified pixel canvas to get complete pixel coverage.
        Returns (all_pixels, bounds) where bounds = (min_x, max_x, min_y, max_y).
        """
        # Get all pixels from all fixtures that have pixel data
        all_pixels = get_all_pixel_positions(fixtures)
        
        if not all_pixels:
            return [], (0, 1, 0, 1)
        
        min_x = min(p['canvas_x'] for p in all_pixels)
        max_x = max(p['canvas_x'] for p in all_pixels)
        min_y = min(p['canvas_y'] for p in all_pixels)
        max_y = max(p['canvas_y'] for p in all_pixels)
        
        # Ensure non-zero ranges — expand symmetrically (centre at 0.5)
        if max_x - min_x < 0.001:
            mid_x = (min_x + max_x) * 0.5
            min_x = mid_x - 0.05
            max_x = mid_x + 0.05
        if max_y - min_y < 0.001:
            mid_y = (min_y + max_y) * 0.5
            min_y = mid_y - 0.05
            max_y = mid_y + 0.05
        
        return all_pixels, (min_x, max_x, min_y, max_y)

    def _apply_ensemble_ocean(self, fixtures: list, effect: EffectParameters, phase: float):
        """Ocean waves - pixels show water, movers sway like kelp, others pulse with tide."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ocean']
        
        # Use 2*pi for smooth looping (full sine cycle per phase 0->1)
        tau = 2 * math.pi
        
        # Tide position (slow oscillation) - completes full cycle
        tide = (math.sin(phase * tau) + 1) / 2  # 0 to 1
        
        # === PIXEL FIXTURES: Ocean waves ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Multiple wave layers - use integer multipliers for smooth looping
            wave1 = math.sin((nx * 4 + phase * 2) * tau) * 0.15
            wave2 = math.sin((nx * 6 - phase * 2) * tau) * 0.1
            surface = 0.3 + wave1 + wave2
            
            # Depth coloring
            color_pos = (ny * 0.6 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = max(0.4, min(1.0, 0.7 + (surface - ny) * 2))
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Slow sway like underwater kelp ===
        for i, fixture in enumerate(cats['movers']):
            # Each mover sways with phase offset - use full tau cycle
            offset = i * 0.618
            sway_x = math.sin((phase + offset) * tau) * 30  # ±30° pan
            sway_y = math.sin((phase + offset * 0.7) * tau) * 15  # ±15° tilt
            
            # Color follows tide
            color_pos = (tide + i * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Intensity pulses with waves - full cycle
            wave_intensity = 0.5 + 0.5 * math.sin((phase * 2 + i * 0.3) * tau)
            
            self._apply_mover_position(fixture, sway_x, sway_y, r, g, b, 
                                       intensity_scale * wave_intensity,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH/OTHER: Pulse with tide ===
        for fixture in cats['wash'] + cats['other']:
            color_pos = (tide + 0.3) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            brightness = 0.4 + tide * 0.6
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}", 
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_aurora(self, fixtures: list, effect: EffectParameters, phase: float):
        """Northern lights - coordinated curtains across all fixtures."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['aurora']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === PIXEL FIXTURES: Aurora curtains ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Vertical curtains that sway - full cycle
            sway = math.sin(phase * tau + nx * 3) * 0.15
            curtain_x = nx + sway
            
            curtain1 = math.sin((curtain_x * 5 + phase) * tau)
            curtain2 = math.sin((curtain_x * 7 - phase) * tau) * 0.7
            
            shimmer = math.sin((ny * 8 + phase * 3) * tau) * 0.1
            intensity = max(0, (curtain1 + curtain2 + 2) / 4 + shimmer)
            
            v_fade = 1.0 - ny * 0.4
            
            color_pos = (curtain_x * 0.4 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * intensity * v_fade)
        
        # === MOVERS: Slow sweeping arcs following the aurora ===
        for i, fixture in enumerate(cats['movers']):
            # Sweep across like aurora curtain - use full phase with offset
            sweep_phase = (phase + i * 0.25) % 1.0
            pan_angle = math.sin(sweep_phase * tau) * 60  # ±60° pan
            
            # Gentle vertical wave - full cycle
            tilt_angle = 20 + math.sin((phase + i * 0.3) * tau) * 25
            
            # Color matches aurora
            color_pos = (sweep_phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Brightness pulses with curtains - full cycle
            brightness = 0.4 + 0.6 * ((math.sin((phase * 2 + i * 0.5) * tau) + 1) / 2)
            
            self._apply_mover_position(fixture, pan_angle, tilt_angle, r, g, b,
                                       intensity_scale * brightness,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH/OTHER: Ambient aurora glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Gentle pulsing - full cycle
            brightness = 0.5 + 0.3 * math.sin((phase + i * 0.4) * tau)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_breathing(self, fixtures: list, effect: EffectParameters, phase: float):
        """Synchronized breathing - all fixtures inhale/exhale together."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES.get(
            getattr(effect, 'palette', 'pastel'), 
            self.GRADIENT_PALETTES['pastel']
        )
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Breathing curve uses smooth sine-based breathing (inhale/exhale)
        # Full cycle: inhale from 0-0.5, exhale from 0.5-1.0
        breath = (math.sin((phase - 0.25) * tau) + 1) / 2  # Smooth 0->1->0 over full cycle
        
        master_brightness = 0.2 + breath * 0.8
        
        # Color slowly cycles - full phase
        base_color_pos = phase
        
        # === PIXEL FIXTURES: Radial breathing from center ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Distance from center
            dist = ((nx - 0.5) ** 2 + (ny - 0.5) ** 2) ** 0.5
            
            # Breathing expands from center
            breath_wave = max(0, 1 - abs(dist - breath * 0.7) * 4)
            
            color_pos = (base_color_pos + dist * 0.3) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.3 + breath_wave * 0.7
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness * master_brightness)
        
        # === MOVERS: Breathe in position - expand on inhale, contract on exhale ===
        for i, fixture in enumerate(cats['movers']):
            # Spread out on inhale
            angle_offset = (i / max(1, len(cats['movers']))) * 360
            spread = breath * 45  # 0° to 45° spread
            
            pan_angle = math.sin(math.radians(angle_offset)) * spread
            tilt_angle = 30 - breath * 20  # Tilt up on inhale
            
            color_pos = (base_color_pos + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, pan_angle, tilt_angle, r, g, b,
                                       intensity_scale * master_brightness,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH/OTHER: Simple breathing ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (base_color_pos + i * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(master_brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_spotlight_dance(self, fixtures: list, effect: EffectParameters, phase: float):
        """Spotlight dance - movers sweep while pixels create floor patterns."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['sunset']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === MOVERS: Elegant sweeping patterns ===
        num_movers = max(1, len(cats['movers']))
        for i, fixture in enumerate(cats['movers']):
            # Figure-8 or circular patterns offset by mover index
            mover_phase = (phase + i / num_movers) % 1.0
            
            # Smooth figure-8 - use full tau cycle
            pan_angle = math.sin(mover_phase * tau) * 50
            tilt_angle = 25 + math.sin(mover_phase * 2 * tau) * 20
            
            # Color cycles through warm tones
            color_pos = (mover_phase + i * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Brightness varies smoothly - full cycle
            brightness = 0.6 + 0.4 * math.sin((mover_phase + 0.25) * tau)
            
            self._apply_mover_position(fixture, pan_angle, tilt_angle, r, g, b,
                                       intensity_scale * brightness,
                                       fixture_index=i, phase_offset=phase)
        
        # === PIXEL FIXTURES: Follow the spotlight positions ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        
        # Create spotlight positions on pixel canvas matching movers
        spotlights = []
        for i in range(num_movers):
            mover_phase = (phase + i / num_movers) % 1.0
            sx = 0.5 + math.sin(mover_phase * tau) * 0.35
            sy = 0.5 + math.sin(mover_phase * 2 * tau) * 0.25
            spotlights.append((sx, sy, mover_phase))
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Brightness from nearest spotlight
            brightness = 0.1  # Ambient
            color_blend = 0.0
            
            for j, (sx, sy, sp) in enumerate(spotlights):
                dist = ((nx - sx) ** 2 + (ny - sy) ** 2) ** 0.5
                spot_brightness = math.exp(-dist * dist * 12)
                brightness += spot_brightness * 0.5
                color_blend += spot_brightness * sp
            
            brightness = min(1.0, brightness)
            color_pos = (color_blend + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === WASH/OTHER: Ambient warm glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            brightness = 0.4 + 0.2 * math.sin((phase * 2 + i * 0.3) * tau)
            
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_galaxy(self, fixtures: list, effect: EffectParameters, phase: float):
        """Galaxy - movers orbit center, pixels show spiral arms, others twinkle."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['galaxy']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Galaxy rotation - full cycle
        rotation = phase * tau
        
        # === PIXEL FIXTURES: Spiral galaxy ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Convert to polar from center
            cx, cy = nx - 0.5, ny - 0.5
            dist = (cx ** 2 + cy ** 2) ** 0.5
            angle = math.atan2(cy, cx) + rotation
            
            # Spiral arms
            spiral = (angle / tau + dist * 2) % 1.0
            arm_intensity = (math.sin(spiral * 2 * tau) + 1) / 2
            
            # Core glow
            core_glow = math.exp(-dist * 5)
            
            color_pos = (spiral + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = max(0.1, min(1.0, arm_intensity * 0.6 + core_glow * 0.5))
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Orbit around center ===
        for i, fixture in enumerate(cats['movers']):
            # Orbital motion - full cycle per phase
            orbit_radius = 40 + i * 15  # Different orbit radii
            orbit_phase = (phase + i * 0.3) % 1.0
            
            pan_angle = math.sin(orbit_phase * tau) * orbit_radius
            tilt_angle = 35 + math.cos(orbit_phase * tau) * 15
            
            color_pos = (orbit_phase + i * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Twinkle as they orbit - full cycle
            twinkle = 0.6 + 0.4 * math.sin((phase * 3 + i * 2) * tau)
            
            self._apply_mover_position(fixture, pan_angle, tilt_angle, r, g, b,
                                       intensity_scale * twinkle,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH/OTHER: Twinkling stars ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            # Each fixture twinkles - full cycle
            twinkle_phase = (phase * 2 + i * 0.618) % 1.0
            twinkle = (math.sin(twinkle_phase * tau) + 1) / 2
            
            color_pos = (i * 0.15 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.2 + twinkle * 0.6
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_storm(self, fixtures: list, effect: EffectParameters, phase: float):
        """Thunderstorm - lightning flashes, movers search, pixels rain."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Storm colors
        storm_palette = [(70, 70, 90), (80, 90, 110), (60, 70, 85), (90, 100, 120), (75, 80, 95)]
        
        # Lightning timing (random-ish based on phase) - use integer cycle count
        lightning_cycle = (phase * 4) % 1.0  # 4 lightning cycles per phase
        is_lightning = lightning_cycle < 0.08 or (lightning_cycle > 0.12 and lightning_cycle < 0.18)
        lightning_intensity = 1.0 if is_lightning else 0.0
        
        # === PIXEL FIXTURES: Rain falling ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Rain drops falling - continuous loop
            rain_col = (i * 7) % 11 < 3  # ~27% are rain columns
            drop_phase = ((phase * 2 - ny + nx * 0.1 + i * 0.01) % 1.0)
            
            if rain_col and drop_phase < 0.15:
                # Raindrop
                rain_brightness = 1.0 - drop_phase / 0.15
                r, g, b = 150, 180, 220  # Rain blue
            else:
                # Dark sky with lightning flash
                color_pos = (nx * 0.2 + phase) % 1.0
                r, g, b = self._interpolate_palette_color(storm_palette, color_pos)
                rain_brightness = 0.3 + lightning_intensity * 0.7
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * rain_brightness)
        
        # === MOVERS: Searching/sweeping like searchlights in storm ===
        for i, fixture in enumerate(cats['movers']):
            # Erratic movement - use full tau cycles
            search_phase = (phase + i * 0.4) % 1.0
            
            # Jittery pan/tilt - use integer multipliers with tau
            pan_angle = math.sin(search_phase * 2 * tau) * 50 + \
                       math.sin(search_phase * 4 * tau) * 15
            tilt_angle = 30 + math.sin(search_phase * 3 * tau) * 20
            
            # Dim blue-white, bright on lightning
            if is_lightning:
                r, g, b = 255, 255, 255
                brightness = 1.0
            else:
                r, g, b = 100, 120, 150
                brightness = 0.4
            
            self._apply_mover_position(fixture, pan_angle, tilt_angle, r, g, b,
                                       intensity_scale * brightness,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH/OTHER: Flash with lightning ===
        for fixture in cats['wash'] + cats['other']:
            if is_lightning:
                self.apply_static([fixture], "#ffffff", 
                                int(intensity_scale * 100), skip_pan_tilt=True)
            else:
                self.apply_static([fixture], "#3a3a4a",
                                int(intensity_scale * 30), skip_pan_tilt=True)
    
    def _apply_ensemble_fireplace(self, fixtures: list, effect: EffectParameters, phase: float):
        """Cozy fireplace - warm flickering across all fixtures."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Fire colors
        fire_palette = [(255, 80, 0), (255, 120, 20), (255, 160, 40), (255, 100, 10), (255, 140, 30)]
        
        # Global flicker - use integer multipliers for smooth loop
        flicker1 = math.sin(phase * 4 * tau) * 0.1
        flicker2 = math.sin(phase * 6 * tau) * 0.07
        flicker3 = math.sin(phase * 3 * tau) * 0.12
        master_flicker = 0.7 + flicker1 + flicker2 + flicker3
        
        # === PIXEL FIXTURES: Fire with rising flames ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Flames rise from bottom
            flame_base = 1.0 - ny
            
            # Flickering flames - continuous
            flame_flicker = math.sin(phase * 8 * tau + nx * 8 + i * 0.3) * 0.15
            flame_flicker += math.sin(phase * 12 * tau + nx * 12) * 0.1
            
            brightness = max(0.1, min(1.0, flame_base + flame_flicker))
            
            # Color based on height (hotter at bottom)
            color_pos = (ny * 0.6 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(fire_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness * master_flicker)
        
        # === MOVERS: Gentle sway like flames ===
        for i, fixture in enumerate(cats['movers']):
            # Gentle sway - use full tau cycles
            sway_x = math.sin((phase + i * 0.3) * tau) * 15
            sway_x += math.sin((phase * 2 + i * 0.2) * tau) * 8
            sway_y = math.sin((phase + i * 0.25) * tau) * 10
            
            color_pos = (i * 0.2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(fire_palette, color_pos)
            
            # Flickering brightness - full cycle
            fixture_flicker = 0.6 + 0.4 * math.sin((phase * 5 + i * 0.5) * tau)
            
            self._apply_mover_position(fixture, sway_x, sway_y + 20, r, g, b,
                                       intensity_scale * master_flicker * fixture_flicker,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH/OTHER: Warm flickering glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (i * 0.15 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(fire_palette, color_pos)
            
            fixture_flicker = 0.5 + 0.3 * math.sin((phase * 6 + i * 0.5) * tau)
            
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(fixture_flicker * master_flicker * intensity_scale * 100), 
                            skip_pan_tilt=True)
    
    def _apply_ensemble_midnight(self, fixtures: list, effect: EffectParameters, phase: float):
        """Midnight blue - slow, mysterious, movers scan slowly."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['midnight']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === PIXEL FIXTURES: Slow drifting midnight clouds ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Slow drifting patterns - use full tau cycles
            drift1 = math.sin((nx * 2 + phase) * tau) * math.cos((ny * 1.5) * tau)
            drift2 = math.cos((nx * 1.5 + phase) * tau) * math.sin((ny * 2) * tau)
            
            drift = (drift1 + drift2 + 2) / 4
            
            color_pos = (drift * 0.5 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.4 + drift * 0.4
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Very slow sweeping ===
        for i, fixture in enumerate(cats['movers']):
            # Slow, deliberate movement - full cycle
            slow_phase = (phase + i * 0.25) % 1.0
            
            pan_angle = math.sin(slow_phase * tau) * 40
            tilt_angle = 30 + math.sin(slow_phase * tau) * 20
            
            color_pos = (slow_phase + i * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Gentle fade in/out - full cycle
            brightness = 0.3 + 0.5 * (math.sin(slow_phase * tau) + 1) / 2
            
            self._apply_mover_position(fixture, pan_angle, tilt_angle, r, g, b,
                                       intensity_scale * brightness,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH/OTHER: Low ambient ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Very subtle pulsing - full cycle
            brightness = 0.3 + 0.15 * math.sin((phase + i * 0.3) * tau)
            
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_carnival(self, fixtures: list, effect: EffectParameters, phase: float):
        """Carnival - vibrant colors, movers dance, pixels chase."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Bright carnival colors
        carnival_palette = [(255, 0, 100), (255, 200, 0), (0, 255, 150), 
                          (255, 100, 0), (150, 0, 255), (0, 200, 255)]
        
        # === PIXEL FIXTURES: Chasing rainbow ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Fast chase pattern
            chase_pos = (nx + phase) % 1.0
            
            # Color bands
            color_idx = int(chase_pos * len(carnival_palette)) % len(carnival_palette)
            r, g, b = carnival_palette[color_idx]
            
            # Brightness pulses - full cycle
            pulse = 0.7 + 0.3 * math.sin((chase_pos + phase * 2) * tau)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * pulse)
        
        # === MOVERS: Dancing movement ===
        for i, fixture in enumerate(cats['movers']):
            # Energetic but smooth movement - full cycle
            dance_phase = (phase + i * 0.3) % 1.0
            
            pan_angle = math.sin(dance_phase * 2 * tau) * 55
            tilt_angle = 35 + math.sin(dance_phase * 3 * tau) * 25
            
            # Cycle through colors
            color_idx = int((phase * len(carnival_palette) + i) % len(carnival_palette))
            r, g, b = carnival_palette[color_idx]
            
            self._apply_mover_position(fixture, pan_angle, tilt_angle, r, g, b,
                                       intensity_scale * 0.9,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH/OTHER: Color cycle ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_idx = int((phase * len(carnival_palette) + i * 0.5) % len(carnival_palette))
            r, g, b = carnival_palette[color_idx]
            
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 80), skip_pan_tilt=True)
    
    def _apply_ensemble_meditation_room(self, fixtures: list, effect: EffectParameters, phase: float):
        """Meditation room - extremely slow, calming, minimal movement."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Calming lavender/soft colors
        calm_palette = [(180, 160, 200), (160, 180, 200), (200, 180, 190), 
                       (170, 190, 200), (190, 170, 195)]
        
        # Smooth breathing using sine - full cycle for seamless loop
        breath = (math.sin((phase - 0.25) * tau) + 1) / 2  # 0->1->0 over full phase
        master_brightness = 0.3 + breath * 0.4  # Keep it dim and calm
        
        # === PIXEL FIXTURES: Gentle glow, almost static ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Very subtle variation
            color_pos = (nx * 0.1 + ny * 0.1 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(calm_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * master_brightness)
        
        # === MOVERS: Nearly still, very subtle drift ===
        for i, fixture in enumerate(cats['movers']):
            # Extremely slow drift - full cycle
            drift = math.sin((phase + i * 0.5) * tau) * 5  # Just ±5°
            
            pan_angle = drift
            tilt_angle = 30 + math.sin((phase + i * 0.3) * tau) * 3
            
            color_pos = (i * 0.15 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(calm_palette, color_pos)
            
            self._apply_mover_position(fixture, pan_angle, tilt_angle, r, g, b,
                                       intensity_scale * master_brightness * 0.8,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH/OTHER: Soft ambient ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (i * 0.1 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(calm_palette, color_pos)
            
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(master_brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_forest(self, fixtures: list, effect: EffectParameters, phase: float):
        """Forest canopy - dappled light, movers sway like branches."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['forest']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Wind simulation - full cycle
        wind = math.sin(phase * tau) * 0.5 + math.sin(phase * 2 * tau) * 0.3
        
        # === PIXELS: Dappled sunlight through leaves ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Leaf shadows moving with wind - full cycles
            shadow1 = math.sin((nx * 6 + wind * 2 + phase) * tau) * 0.3
            shadow2 = math.cos((ny * 4 + wind * 1.5 + phase) * tau) * 0.2
            
            dapple = 0.5 + shadow1 + shadow2
            dapple = max(0.2, min(1.0, dapple))
            
            color_pos = (nx * 0.3 + ny * 0.3 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * dapple)
        
        # === MOVERS: Sway like tree branches ===
        for i, fixture in enumerate(cats['movers']):
            branch_sway = wind * 20 + math.sin((phase + i * 0.5) * tau) * 10
            tilt_sway = math.sin((phase + i * 0.7) * tau) * 8
            
            color_pos = (i * 0.2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, branch_sway, 35 + tilt_sway, r, g, b,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH/OTHER: Forest floor ambient ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            brightness = 0.4 + 0.2 * math.sin((phase + i * 0.3) * tau)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_sunset(self, fixtures: list, effect: EffectParameters, phase: float):
        """Golden hour sunset - warm colors spreading across all fixtures."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['sunset']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Sun position (moves in a smooth arc over time) - full cycle
        sun_x = 0.5 + math.cos(phase * tau) * 0.4
        sun_y = 0.3 + math.sin(phase * tau) * 0.15
        
        # === PIXELS: Sunset gradient ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Distance from "sun"
            sun_dist = ((nx - sun_x) ** 2 + (ny - sun_y) ** 2) ** 0.5
            
            # Color shifts from warm yellow near sun to deep red/purple away
            color_pos = min(1.0, sun_dist * 1.5)
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Glow near sun
            glow = math.exp(-sun_dist * 3) * 0.5
            brightness = 0.5 + glow
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Track towards sun position ===
        for i, fixture in enumerate(cats['movers']):
            # Point loosely towards sun - full cycle
            target_pan = (sun_x - 0.5) * 80 + math.sin((phase + i * 0.4) * tau) * 10
            target_tilt = 30 + sun_y * 20
            
            color_pos = (i * 0.15 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, target_pan, target_tilt, r, g, b,
                                       intensity_scale * 0.8,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Warm sunset glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 70), skip_pan_tilt=True)
    
    def _apply_ensemble_underwater(self, fixtures: list, effect: EffectParameters, phase: float):
        """Deep underwater - caustics, bubbles, slow movements."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Deep ocean colors
        deep_palette = [(0, 40, 80), (0, 60, 100), (0, 80, 120), (20, 100, 140), (40, 120, 160)]
        
        # === PIXELS: Caustic light patterns ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Caustic patterns (overlapping sine waves) - full cycles
            c1 = math.sin((nx * 8 + phase) * tau) * math.cos((ny * 6 - phase) * tau)
            c2 = math.sin((nx * 5 - phase) * tau) * math.cos((ny * 7 + phase) * tau)
            caustic = (c1 + c2 + 2) / 4
            
            # Rising bubbles (occasional bright spots)
            bubble_phase = ((ny + phase + i * 0.1) % 1.0)
            bubble = math.exp(-((bubble_phase - 0.5) ** 2) * 50) if (i % 7) == 0 else 0
            
            brightness = 0.3 + caustic * 0.5 + bubble * 0.3
            color_pos = (ny * 0.5 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(deep_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Slow drift like floating ===
        for i, fixture in enumerate(cats['movers']):
            drift_x = math.sin((phase + i * 0.6) * tau) * 25
            drift_y = math.sin((phase + i * 0.4) * tau) * 15
            
            color_pos = (i * 0.2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(deep_palette, color_pos)
            
            self._apply_mover_position(fixture, drift_x, 40 + drift_y, r, g, b,
                                       intensity_scale * 0.6,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Deep ambient glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(deep_palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 50), skip_pan_tilt=True)
    
    def _apply_ensemble_lava(self, fixtures: list, effect: EffectParameters, phase: float):
        """Flowing lava - hot reds and oranges flowing slowly."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['lava']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === PIXELS: Flowing lava ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Lava flow pattern - full cycles
            flow = math.sin((nx * 3 + phase) * tau) * 0.2
            flow += math.sin((ny * 2 - phase) * tau) * 0.15
            
            # Hot spots
            hot = math.sin((nx * 5 + ny * 4 + phase) * tau)
            hot = max(0, hot) ** 2 * 0.3
            
            brightness = 0.5 + flow + hot
            color_pos = (flow + hot + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Slow, heavy movement ===
        for i, fixture in enumerate(cats['movers']):
            # Heavy, deliberate movement like cooling lava - full cycle
            pan = math.sin((phase + i * 0.4) * tau) * 30
            tilt = 35 + math.sin((phase + i * 0.3) * tau) * 10
            
            color_pos = (i * 0.2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.6 + 0.3 * math.sin((phase * 2 + i * 0.5) * tau)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * brightness,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Hot glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            brightness = 0.5 + 0.3 * math.sin((phase + i * 0.4) * tau)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_ice(self, fixtures: list, effect: EffectParameters, phase: float):
        """Frozen ice cave - cold blues with crystalline shimmer."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ice']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === PIXELS: Ice crystals with shimmer ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Crystal facets - full cycles
            facet = abs(math.sin((nx * 10 + phase) * tau) * 
                       math.cos((ny * 8 - phase) * tau))
            
            # Shimmer sparkle
            shimmer = 0
            if (i + int(phase * 10)) % 13 == 0:
                shimmer = 0.5 * ((math.sin(phase * 5 * tau) + 1) / 2) ** 2
            
            brightness = 0.4 + facet * 0.4 + shimmer
            color_pos = (nx * 0.3 + ny * 0.2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Slow, precise movements ===
        for i, fixture in enumerate(cats['movers']):
            # Sharp, angular movements like ice - full cycles
            pan = math.sin((phase + i * 0.5) * tau) * 35
            tilt = 30 + math.cos((phase + i * 0.4) * tau) * 15
            
            color_pos = (i * 0.15 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Cold ambient ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 60), skip_pan_tilt=True)
    
    def _apply_ensemble_candy(self, fixtures: list, effect: EffectParameters, phase: float):
        """Candy shop - sweet pastels in playful patterns."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['candy']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === PIXELS: Swirling candy colors ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Swirl pattern - full cycle
            cx, cy = nx - 0.5, ny - 0.5
            angle = math.atan2(cy, cx) + phase * tau
            dist = (cx ** 2 + cy ** 2) ** 0.5
            
            swirl = (angle / tau + dist * 2 + phase) % 1.0
            
            color_pos = swirl
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.6 + 0.3 * math.sin((dist * 8 + phase) * tau)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Playful bouncing ===
        for i, fixture in enumerate(cats['movers']):
            bounce = abs(math.sin((phase + i * 0.3) * tau))
            pan = math.sin((phase + i * 0.4) * tau) * 40
            tilt = 25 + bounce * 20
            
            color_pos = (phase + i * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.85,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Bright candy colors ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 75), skip_pan_tilt=True)
    
    def _apply_ensemble_neon(self, fixtures: list, effect: EffectParameters, phase: float):
        """Neon city - vibrant glowing signs."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['neon']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === PIXELS: Neon sign flicker ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Different "signs" (bands)
            band = int(nx * 5) % 5
            band_phase = (phase + band * 0.2) % 1.0
            
            # Occasional flicker - controlled
            flicker = 1.0
            if (i + int(phase * 15)) % 17 == 0:
                flicker = 0.3 + 0.7 * ((math.sin(phase * 10 * tau) + 1) / 2)
            
            color_pos = (band * 0.2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            brightness = 0.7 * flicker + 0.2 * math.sin((band_phase + ny) * tau)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * max(0.3, brightness))
        
        # === MOVERS: Scan like searching ===
        for i, fixture in enumerate(cats['movers']):
            scan = math.sin((phase + i * 0.3) * tau) * 50
            tilt = 35 + math.sin((phase + i * 0.5) * tau) * 15
            
            color_pos = (phase + i * 0.25) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, scan, tilt, r, g, b,
                                       intensity_scale * 0.9,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Neon glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 80), skip_pan_tilt=True)
    
    def _apply_ensemble_earth(self, fixtures: list, effect: EffectParameters, phase: float):
        """Earth tones - warm browns and greens, organic movement."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['earth']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === PIXELS: Organic, earthy patterns ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Organic noise-like pattern - full cycles
            pattern = math.sin((nx * 4 + phase) * tau) * \
                     math.cos((ny * 3 + phase) * tau) * 0.3
            pattern += math.sin((nx * 2 + ny * 2 + phase) * tau) * 0.2
            
            brightness = 0.5 + pattern
            color_pos = (nx * 0.4 + ny * 0.3 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Grounded, slow movement ===
        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase + i * 0.4) * tau) * 25
            tilt = 40 + math.sin((phase + i * 0.3) * tau) * 10
            
            color_pos = (i * 0.2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.65,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Warm earth glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 55), skip_pan_tilt=True)
    
    def _apply_ensemble_tropical(self, fixtures: list, effect: EffectParameters, phase: float):
        """Tropical paradise - bright vibrant island colors."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['tropical']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === PIXELS: Tropical waves ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Waves of tropical color - full cycles
            wave = math.sin((nx * 3 + phase) * tau) * 0.2
            wave += math.sin((ny * 2 - phase) * tau) * 0.15
            
            brightness = 0.6 + wave + 0.2
            color_pos = (nx * 0.5 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Swaying palm tree motion ===
        for i, fixture in enumerate(cats['movers']):
            sway = math.sin((phase + i * 0.4) * tau) * 35
            sway += math.sin((phase * 2 + i * 0.2) * tau) * 10
            tilt = 30 + math.sin((phase + i * 0.5) * tau) * 12
            
            color_pos = (phase + i * 0.18) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, sway, tilt, r, g, b,
                                       intensity_scale * 0.8,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Bright tropical ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 75), skip_pan_tilt=True)
    
    def _apply_ensemble_clockwork(self, fixtures: list, effect: EffectParameters, phase: float):
        """Clockwork - precise mechanical movements, ticking patterns."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Brass/copper colors
        clock_palette = [(180, 140, 80), (200, 160, 100), (160, 120, 60), (220, 180, 120), (140, 100, 40)]
        
        # Tick phase (discrete steps)
        tick = int(phase * 8) / 8.0
        tick_progress = (phase * 8) % 1.0
        
        # === PIXELS: Gear patterns ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Multiple gears
            cx, cy = nx - 0.5, ny - 0.5
            angle = math.atan2(cy, cx)
            dist = (cx ** 2 + cy ** 2) ** 0.5
            
            # Gear teeth
            gear1 = math.sin((angle + tick * 2 * math.pi) * 8) * 0.3
            gear2 = math.sin((angle - tick * 2 * math.pi) * 6 + math.pi) * 0.2
            
            gear = 0.5 + (gear1 if dist < 0.3 else gear2)
            
            color_pos = (dist + tick * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(clock_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * gear)
        
        # === MOVERS: Precise ticking movement ===
        for i, fixture in enumerate(cats['movers']):
            # Step-wise movement
            target_pan = math.sin(tick * 2 * math.pi + i * 0.5) * 45
            current_pan = target_pan + (math.sin(tick * 2 * math.pi + i * 0.5 + 0.1) * 45 - target_pan) * (1 - tick_progress)
            
            target_tilt = 30 + math.cos(tick * 2 * math.pi + i * 0.3) * 15
            
            color_pos = (i * 0.2 + tick * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(clock_palette, color_pos)
            
            self._apply_mover_position(fixture, current_pan, target_tilt, r, g, b,
                                       intensity_scale * 0.75,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Warm brass glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (tick * 0.15 + i * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(clock_palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 60), skip_pan_tilt=True)
    
    def _apply_ensemble_starfield(self, fixtures: list, effect: EffectParameters, phase: float):
        """Starfield - traveling through space."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Space colors
        space_palette = [(255, 255, 255), (200, 200, 255), (255, 200, 200), (200, 255, 200), (255, 255, 200)]
        
        # === PIXELS: Stars streaming past ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Star positions radiate from center
            cx, cy = nx - 0.5, ny - 0.5
            dist = (cx ** 2 + cy ** 2) ** 0.5
            
            # Stars stream outward - use full phase cycle
            star_phase = (dist - phase + i * 0.02) % 0.3
            is_star = star_phase < 0.03
            
            if is_star:
                brightness = 1.0 - star_phase / 0.03
                color_idx = i % len(space_palette)
                r, g, b = space_palette[color_idx]
            else:
                brightness = 0.05  # Dark space
                r, g, b = 10, 10, 30
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Point forward, slight sway ===
        for i, fixture in enumerate(cats['movers']):
            sway_x = math.sin((phase + i * 0.5) * tau) * 15
            sway_y = math.sin((phase + i * 0.4) * tau) * 10
            
            r, g, b = space_palette[i % len(space_palette)]
            
            self._apply_mover_position(fixture, sway_x, 35 + sway_y, r, g, b,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Deep space ambient ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            twinkle = 0.3 + 0.4 * max(0, math.sin((phase * 3 + i * 1.2) * tau))
            r, g, b = space_palette[i % len(space_palette)]
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(twinkle * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_heartbeat_sync(self, fixtures: list, effect: EffectParameters, phase: float):
        """Heartbeat sync - all fixtures pulse with heartbeat rhythm."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Heartbeat pattern (lub-dub)
        beat_phase = phase % 1.0
        if beat_phase < 0.1:  # First beat
            beat = (beat_phase / 0.1) ** 2
        elif beat_phase < 0.2:  # First recovery
            beat = 1.0 - ((beat_phase - 0.1) / 0.1) ** 0.5
        elif beat_phase < 0.3:  # Second beat (smaller)
            beat = 0.7 * ((beat_phase - 0.2) / 0.1) ** 2
        elif beat_phase < 0.4:  # Second recovery
            beat = 0.7 * (1.0 - ((beat_phase - 0.3) / 0.1) ** 0.5)
        else:  # Rest
            beat = 0.1
        
        # Heart colors
        heart_palette = [(255, 50, 80), (255, 80, 100), (255, 100, 120), (200, 40, 60), (180, 30, 50)]
        
        # === PIXELS: Pulse from center ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            cx, cy = nx - 0.5, ny - 0.5
            dist = (cx ** 2 + cy ** 2) ** 0.5
            
            # Pulse wave
            wave_pos = (beat_phase * 2 - dist * 3) % 1.0
            wave = math.exp(-wave_pos * 5) if wave_pos > 0 else 0
            
            brightness = 0.2 + beat * 0.5 + wave * 0.3
            color_pos = (dist + beat_phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(heart_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Pulse inward/outward ===
        for i, fixture in enumerate(cats['movers']):
            angle = (i / max(1, len(cats['movers']))) * 2 * math.pi
            spread = beat * 30
            
            pan = math.sin(angle) * spread
            tilt = 35 - beat * 10
            
            color_pos = (i * 0.15 + beat_phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(heart_palette, color_pos)
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * (0.4 + beat * 0.6),
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Beat flash ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (i * 0.1 + beat_phase * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(heart_palette, color_pos)
            brightness = 0.3 + beat * 0.7
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_wave_pool(self, fixtures: list, effect: EffectParameters, phase: float):
        """Wave pool - concentric ripples spreading out."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ocean']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === PIXELS: Concentric waves ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            cx, cy = nx - 0.5, ny - 0.5
            dist = (cx ** 2 + cy ** 2) ** 0.5
            
            # Multiple wave sources - full cycles
            wave1 = math.sin((dist * 10 - phase * 2) * tau) * 0.3
            wave2 = math.sin((dist * 8 - phase * 2 + 1) * tau) * 0.2
            
            brightness = 0.5 + wave1 + wave2
            color_pos = (dist + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Bob up and down with waves ===
        for i, fixture in enumerate(cats['movers']):
            wave_offset = math.sin((phase * 2 + i * 0.5) * tau)
            pan = math.sin((phase + i * 0.4) * tau) * 20
            tilt = 35 + wave_offset * 15
            
            color_pos = (phase + i * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * (0.6 + wave_offset * 0.2),
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Gentle wave glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            wave = math.sin((phase * 2 + i * 0.4) * tau) * 0.2
            color_pos = (phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            brightness = 0.5 + wave
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_pendulum(self, fixtures: list, effect: EffectParameters, phase: float):
        """Pendulum - synchronized swinging motion."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Pendulum physics (slows at edges) - full cycle
        swing_angle = math.sin(phase * tau) * 0.8
        swing_pos = (swing_angle + 1) / 2  # 0 to 1
        
        # Warm colors
        pendulum_palette = [(255, 200, 100), (255, 180, 80), (255, 160, 60), (255, 140, 40), (255, 120, 20)]
        
        # === PIXELS: Follow the pendulum ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Light follows pendulum position
            dist = abs(nx - swing_pos)
            brightness = math.exp(-dist * dist * 10) * 0.7 + 0.2
            
            # Trail effect
            trail_dist = abs(nx - swing_pos + swing_angle * 0.1)
            trail = math.exp(-trail_dist * trail_dist * 15) * 0.3
            
            color_pos = (nx + phase) % 1.0
            r, g, b = self._interpolate_palette_color(pendulum_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * (brightness + trail))
        
        # === MOVERS: Swing in unison ===
        for i, fixture in enumerate(cats['movers']):
            # All movers swing together
            pan = swing_angle * 60
            tilt = 35 + abs(swing_angle) * 10  # Rises at edges
            
            color_pos = (swing_pos + i * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(pendulum_palette, color_pos)
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.8,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Ambient glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (swing_pos + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(pendulum_palette, color_pos)
            brightness = 0.4 + abs(swing_angle) * 0.3
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_lighthouse(self, fixtures: list, effect: EffectParameters, phase: float):
        """Lighthouse - rotating beam sweeps across all fixtures."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Beam angle
        beam_angle = phase * 2 * math.pi
        beam_x = math.cos(beam_angle)
        beam_y = math.sin(beam_angle)
        
        # === PIXELS: Beam sweeps across ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Distance from beam line
            cx, cy = nx - 0.5, ny - 0.5
            dot = cx * beam_x + cy * beam_y
            
            # Beam brightness
            beam_brightness = math.exp(-((dot - 0.3) ** 2) * 20) if dot > 0 else 0
            
            # Ambient fog
            fog = 0.15
            
            brightness = beam_brightness * 0.85 + fog
            
            # White/yellow beam
            r = int(255 * brightness)
            g = int(240 * brightness)
            b = int(200 * brightness)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
        
        # === MOVERS: One or two act as the lighthouse ===
        for i, fixture in enumerate(cats['movers']):
            if i == 0:
                # Main lighthouse beam
                pan = math.degrees(beam_angle) % 360 - 180
                tilt = 30
                brightness = 1.0
            else:
                # Others track the beam
                track_angle = beam_angle + (i * 0.2)
                pan = math.sin(track_angle) * 40
                tilt = 40
                brightness = 0.5
            
            self._apply_mover_position(fixture, pan, tilt, 255, 240, 200,
                                       intensity_scale * brightness,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Flash when beam passes ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            # Flash based on fixture "position"
            fixture_angle = (i / max(1, len(cats['wash'] + cats['other']))) * 2 * math.pi
            angle_diff = abs(math.sin((beam_angle - fixture_angle) / 2))
            flash = math.exp(-angle_diff * angle_diff * 20)
            
            brightness = 0.1 + flash * 0.8
            self.apply_static([fixture], "#fff0c8",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_jellyfish(self, fixtures: list, effect: EffectParameters, phase: float):
        """Jellyfish - pulsing, drifting bioluminescent creatures."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # Bioluminescent colors
        jelly_palette = [(180, 100, 255), (100, 200, 255), (255, 150, 200), (100, 255, 200), (200, 150, 255)]
        
        # Pulse cycle
        pulse = (math.sin(phase * tau) + 1) / 2
        
        # === PIXELS: Multiple jellyfish ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        
        # Define jellyfish positions - full cycles
        num_jellies = 3
        jelly_positions = []
        for j in range(num_jellies):
            jx = 0.3 + 0.4 * math.sin((phase + j * 0.67) * tau)
            jy = 0.3 + 0.4 * math.cos((phase + j * 0.5) * tau)
            jelly_positions.append((jx, jy, j))
        
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            brightness = 0.1  # Dark water
            color_pos = 0.0
            
            for jx, jy, j in jelly_positions:
                dist = ((nx - jx) ** 2 + (ny - jy) ** 2) ** 0.5
                jelly_pulse = (math.sin((phase * 2 + j * 0.5) * tau) + 1) / 2
                
                # Bell shape
                bell = math.exp(-dist * dist * 15) * jelly_pulse
                brightness += bell * 0.4
                color_pos += bell * (j * 0.2)
            
            color_pos = color_pos % 1.0
            r, g, b = self._interpolate_palette_color(jelly_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * min(1.0, brightness))
        
        # === MOVERS: Drift like jellyfish ===
        for i, fixture in enumerate(cats['movers']):
            drift_x = math.sin((phase + i * 0.6) * tau) * 25
            drift_y = math.cos((phase + i * 0.5) * tau) * 15
            
            color_pos = (i * 0.2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(jelly_palette, color_pos)
            
            brightness = 0.5 + pulse * 0.4
            self._apply_mover_position(fixture, drift_x, 35 + drift_y, r, g, b,
                                       intensity_scale * brightness,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Bioluminescent glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase + i * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(jelly_palette, color_pos)
            brightness = 0.3 + pulse * 0.3
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_plasma(self, fixtures: list, effect: EffectParameters, phase: float):
        """Plasma - classic plasma effect across all fixtures."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['rainbow']
        
        # Use 2*pi for smooth looping
        tau = 2 * math.pi
        
        # === PIXELS: Classic plasma ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Classic plasma formula - full cycles
            v1 = math.sin((nx * 4 + phase) * tau)
            v2 = math.sin((ny * 4 + phase) * tau)
            v3 = math.sin(((nx + ny) * 2.5 + phase) * tau)
            v4 = math.sin((((nx - 0.5) ** 2 + (ny - 0.5) ** 2) ** 0.5 * 5 - phase) * tau)
            
            v = (v1 + v2 + v3 + v4 + 4) / 8
            
            color_pos = v % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * 0.85)
        
        # === MOVERS: Smooth flowing movement ===
        for i, fixture in enumerate(cats['movers']):
            plasma_x = math.sin((phase + i * 0.4) * tau)
            plasma_y = math.cos((phase + i * 0.5) * tau)
            
            pan = plasma_x * 45
            tilt = 35 + plasma_y * 15
            
            color_pos = (phase + i * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.8,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Plasma colors ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase * 0.25 + i * 0.18) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 70), skip_pan_tilt=True)
    
    def _apply_ensemble_rain(self, fixtures: list, effect: EffectParameters, phase: float):
        """Rain - drops falling, movers scanning, ambient thunder."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Gray-blue rain colors
        rain_palette = [(100, 120, 150), (80, 100, 130), (120, 140, 170), (90, 110, 140), (110, 130, 160)]
        
        # === PIXELS: Falling rain ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Rain drops at different speeds
            drop_speed = 1.5 + (i % 5) * 0.3
            drop_pos = (ny + phase * drop_speed + nx * 0.2 + i * 0.05) % 1.0
            
            is_drop = drop_pos < 0.08
            brightness = (1.0 - drop_pos / 0.08) if is_drop else 0.2
            
            color_pos = (nx * 0.3 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(rain_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Scan like searching in rain ===
        for i, fixture in enumerate(cats['movers']):
            scan = math.sin((phase * 0.3 + i * 0.4) * 2 * math.pi) * 40
            tilt = 35 + math.sin((phase * 0.2 + i * 0.3) * math.pi) * 10
            
            color_pos = (i * 0.15 + phase * 0.08) % 1.0
            r, g, b = self._interpolate_palette_color(rain_palette, color_pos)
            
            self._apply_mover_position(fixture, scan, tilt, r, g, b,
                                       intensity_scale * 0.6,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Thunder flashes ===
        thunder = 0
        if (phase * 5) % 1.0 < 0.03:
            thunder = 0.7
        
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase * 0.1 + i * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(rain_palette, color_pos)
            brightness = 0.3 + thunder
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_disco_ball(self, fixtures: list, effect: EffectParameters, phase: float):
        """Disco ball - rotating sparkles everywhere."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Rotation
        rotation = phase * 4 * math.pi
        
        # === PIXELS: Sparkle spots from disco ball ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Multiple reflection spots
            brightness = 0.1
            for spot in range(5):
                spot_angle = rotation + spot * (2 * math.pi / 5)
                spot_x = 0.5 + 0.4 * math.cos(spot_angle + i * 0.02)
                spot_y = 0.5 + 0.3 * math.sin(spot_angle * 2 + i * 0.01)
                
                dist = ((nx - spot_x) ** 2 + (ny - spot_y) ** 2) ** 0.5
                brightness += math.exp(-dist * dist * 50) * 0.4
            
            brightness = min(1.0, brightness)
            # White/silver sparkles
            self._apply_color_to_pixel(pixel, 255, 255, 255, intensity_scale * brightness)
        
        # === MOVERS: Spin and point at disco ball area ===
        for i, fixture in enumerate(cats['movers']):
            spin = math.sin(rotation + i * 0.5) * 60
            tilt = 45 + math.cos(rotation * 0.5 + i * 0.3) * 15
            
            # Color wheel effect
            hue = (phase * 0.5 + i * 0.2) % 1.0
            r = int(127.5 * (1 + math.sin(hue * 2 * math.pi)))
            g = int(127.5 * (1 + math.sin((hue + 0.33) * 2 * math.pi)))
            b = int(127.5 * (1 + math.sin((hue + 0.66) * 2 * math.pi)))
            
            self._apply_mover_position(fixture, spin, tilt, r, g, b,
                                       intensity_scale * 0.9,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Flash with rotation ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            flash_phase = (rotation / (2 * math.pi) + i * 0.15) % 1.0
            flash = math.exp(-((flash_phase - 0.5) ** 2) * 10)
            brightness = 0.3 + flash * 0.6
            
            # Cycle colors
            hue = (phase * 0.3 + i * 0.1) % 1.0
            r = int(127.5 * (1 + math.sin(hue * 2 * math.pi)))
            g = int(127.5 * (1 + math.sin((hue + 0.33) * 2 * math.pi)))
            b = int(127.5 * (1 + math.sin((hue + 0.66) * 2 * math.pi)))
            
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_zen_garden(self, fixtures: list, effect: EffectParameters, phase: float):
        """Zen garden - extremely peaceful, minimal movement."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Soft natural colors
        zen_palette = [(200, 190, 170), (180, 200, 180), (190, 180, 160), (170, 190, 190), (210, 200, 180)]
        
        # Very slow breathing
        breath = (math.sin(phase * 0.5 * math.pi) + 1) / 2
        
        # === PIXELS: Gentle ripples in sand ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Very subtle ripples
            ripple = math.sin((nx * 3 + phase * 0.1) * math.pi) * 0.05
            ripple += math.sin((ny * 2 + phase * 0.08) * math.pi) * 0.03
            
            brightness = 0.4 + ripple + breath * 0.15
            color_pos = (nx * 0.2 + ny * 0.2 + phase * 0.02) % 1.0
            r, g, b = self._interpolate_palette_color(zen_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Almost still ===
        for i, fixture in enumerate(cats['movers']):
            # Barely perceptible movement
            drift = math.sin((phase * 0.05 + i * 0.5) * math.pi) * 3
            
            color_pos = (i * 0.15 + phase * 0.03) % 1.0
            r, g, b = self._interpolate_palette_color(zen_palette, color_pos)
            
            self._apply_mover_position(fixture, drift, 35, r, g, b,
                                       intensity_scale * (0.3 + breath * 0.2),
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Soft ambient ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase * 0.04 + i * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(zen_palette, color_pos)
            brightness = 0.3 + breath * 0.15
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_volcano(self, fixtures: list, effect: EffectParameters, phase: float):
        """Volcano - eruption with lava and sparks."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Eruption cycle (builds, erupts, settles)
        eruption_phase = phase % 1.0
        if eruption_phase < 0.7:  # Building
            eruption = eruption_phase / 0.7
        elif eruption_phase < 0.85:  # Erupting
            eruption = 1.0
        else:  # Settling
            eruption = 1.0 - (eruption_phase - 0.85) / 0.15
        
        # Hot colors
        volcano_palette = [(255, 50, 0), (255, 100, 0), (255, 150, 0), (255, 200, 50), (200, 30, 0)]
        
        # === PIXELS: Lava and sparks ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Lava base (bright at bottom)
            lava = max(0, (1 - ny) - 0.3) * eruption
            
            # Flying sparks during eruption
            if eruption > 0.8:
                spark_phase = ((phase * 3 + i * 0.1) % 1.0)
                if spark_phase < 0.2 and (i % 5) == 0:
                    spark_y = 1 - spark_phase * 4
                    if abs(ny - spark_y) < 0.1:
                        lava += 0.5
            
            brightness = 0.2 + lava * 0.8
            color_pos = (ny * 0.5 + eruption * 0.3) % 1.0
            r, g, b = self._interpolate_palette_color(volcano_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Shake during eruption ===
        for i, fixture in enumerate(cats['movers']):
            shake = eruption * 15 * math.sin((phase * 20 + i) * math.pi)
            tilt_shake = eruption * 10 * math.cos((phase * 18 + i * 0.5) * math.pi)
            
            color_pos = (i * 0.2 + eruption * 0.3) % 1.0
            r, g, b = self._interpolate_palette_color(volcano_palette, color_pos)
            
            self._apply_mover_position(fixture, shake, 35 + tilt_shake, r, g, b,
                                       intensity_scale * (0.4 + eruption * 0.6),
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Glow with eruption ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (eruption * 0.5 + i * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(volcano_palette, color_pos)
            brightness = 0.3 + eruption * 0.7
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_constellation(self, fixtures: list, effect: EffectParameters, phase: float):
        """Constellation - stars connected by lines, movers draw patterns."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Star positions (slowly shift)
        stars = []
        for s in range(7):
            sx = 0.2 + 0.6 * (s % 3) / 2 + math.sin((phase * 0.1 + s) * math.pi) * 0.05
            sy = 0.2 + 0.6 * (s // 3) / 2 + math.cos((phase * 0.08 + s * 0.7) * math.pi) * 0.05
            stars.append((sx, sy))
        
        # === PIXELS: Stars and connecting lines ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            brightness = 0.05  # Dark sky
            
            # Check if near a star
            for sx, sy in stars:
                dist = ((nx - sx) ** 2 + (ny - sy) ** 2) ** 0.5
                if dist < 0.05:
                    brightness = max(brightness, 1.0 - dist / 0.05)
            
            # Check if on a connecting line
            twinkle = 0.3 + 0.2 * math.sin((phase * 3 + nx * 10) * math.pi)
            
            # White/blue stars
            r = int(220 + 35 * math.sin(phase * 2))
            g = int(220 + 35 * math.cos(phase * 2))
            b = 255
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness * twinkle)
        
        # === MOVERS: Trace constellation ===
        for i, fixture in enumerate(cats['movers']):
            # Move between stars
            star_idx = int((phase * 2 + i * 0.3) % len(stars))
            next_star_idx = (star_idx + 1) % len(stars)
            
            progress = (phase * 2 + i * 0.3) % 1.0
            
            sx, sy = stars[star_idx]
            nsx, nsy = stars[next_star_idx]
            
            current_x = sx + (nsx - sx) * progress
            current_y = sy + (nsy - sy) * progress
            
            pan = (current_x - 0.5) * 80
            tilt = 30 + current_y * 20
            
            self._apply_mover_position(fixture, pan, tilt, 200, 200, 255,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Subtle star twinkle ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            twinkle = 0.3 + 0.3 * max(0, math.sin((phase * 4 + i * 1.5) * math.pi))
            self.apply_static([fixture], "#c8c8ff",
                            int(twinkle * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_ballroom(self, fixtures: list, effect: EffectParameters, phase: float):
        """Ballroom - elegant waltz movement, warm golden light."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Waltz timing (3/4)
        waltz_beat = (phase * 3) % 1.0
        waltz_accent = 1.0 if waltz_beat < 0.15 else 0.7
        
        # Elegant gold colors
        ballroom_palette = [(255, 220, 150), (255, 200, 120), (255, 180, 100), (250, 210, 140), (245, 190, 110)]
        
        # === PIXELS: Warm golden glow ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Soft gradient
            gradient = 0.7 + (1 - ny) * 0.2
            
            # Gentle shimmer
            shimmer = 0.05 * math.sin((nx * 8 + phase * 1.5) * math.pi)
            
            brightness = gradient + shimmer
            color_pos = (nx * 0.3 + phase * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(ballroom_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Elegant circular waltz ===
        for i, fixture in enumerate(cats['movers']):
            waltz_phase = (phase * 0.5 + i * 0.25) % 1.0
            
            # Elegant circular pattern
            pan = math.sin(waltz_phase * 2 * math.pi) * 35
            tilt = 35 + math.cos(waltz_phase * 2 * math.pi) * 10
            
            # Subtle beat accent
            brightness = 0.7 + waltz_accent * 0.2
            
            color_pos = (waltz_phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(ballroom_palette, color_pos)
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * brightness,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Warm ambient ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase * 0.08 + i * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(ballroom_palette, color_pos)
            brightness = 0.6 + waltz_accent * 0.15
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_waterfall(self, fixtures: list, effect: EffectParameters, phase: float):
        """Waterfall - cascading water effect."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Water blue-green
        water_palette = [(100, 180, 220), (80, 200, 240), (120, 190, 230), (90, 210, 250), (110, 170, 210)]
        
        # === PIXELS: Falling water ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Water streams falling
            stream = math.sin(nx * 12 + i * 0.1) * 0.5 + 0.5
            fall_pos = (ny + phase * 2 + stream * 0.2) % 1.0
            
            # Foam at bottom
            foam = 0
            if ny > 0.85:
                foam = 0.4 * math.sin((nx * 10 + phase * 5) * math.pi) ** 2
            
            brightness = 0.4 + stream * 0.3 + foam
            color_pos = (ny * 0.5 + phase * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(water_palette, color_pos)
            
            # Add white highlights
            if fall_pos < 0.05:
                r = min(255, r + 100)
                g = min(255, g + 100)
                b = min(255, b + 50)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Follow the fall ===
        for i, fixture in enumerate(cats['movers']):
            fall_phase = (phase + i * 0.2) % 1.0
            
            pan = math.sin((fall_phase + i * 0.3) * 2 * math.pi) * 20
            tilt = 25 + fall_phase * 30  # Tilt down with water
            
            color_pos = (fall_phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(water_palette, color_pos)
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.75,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Mist glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase * 0.15 + i * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(water_palette, color_pos)
            
            # Mist pulses
            mist = 0.5 + 0.2 * math.sin((phase * 2 + i * 0.4) * math.pi)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(mist * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_sunrise(self, fixtures: list, effect: EffectParameters, phase: float):
        """Sunrise - gradual color shift from dark to bright."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Sunrise progress (0=dark, 1=full day)
        sunrise = (math.sin((phase - 0.25) * math.pi) + 1) / 2
        
        # Color shift: deep blue -> purple -> orange -> yellow -> white
        if sunrise < 0.25:
            r, g, b = 30 + sunrise * 200, 20 + sunrise * 80, 80 - sunrise * 80
        elif sunrise < 0.5:
            t = (sunrise - 0.25) * 4
            r = 80 + t * 175
            g = 40 + t * 100
            b = 60 - t * 60
        elif sunrise < 0.75:
            t = (sunrise - 0.5) * 4
            r = 255
            g = 140 + t * 100
            b = t * 100
        else:
            t = (sunrise - 0.75) * 4
            r = 255
            g = 240 + t * 15
            b = 100 + t * 155
        
        r, g, b = int(r), int(g), int(b)
        
        # === PIXELS: Horizon gradient ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Brighter at horizon (bottom for sunrise from behind)
            horizon_glow = max(0, 1 - ny * 1.5)
            brightness = 0.3 + sunrise * 0.5 + horizon_glow * 0.3
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Rise with the sun ===
        for i, fixture in enumerate(cats['movers']):
            # Rise up as sun rises
            tilt = 50 - sunrise * 25
            pan = math.sin((phase * 0.1 + i * 0.4) * math.pi) * 15
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * (0.3 + sunrise * 0.6),
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Growing light ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            brightness = 0.2 + sunrise * 0.6
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_moonlight(self, fixtures: list, effect: EffectParameters, phase: float):
        """Moonlight - soft silver glow, gentle shadows."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Silver/blue moonlight colors
        moon_palette = [(180, 190, 210), (160, 175, 200), (200, 205, 220), (170, 185, 205), (190, 195, 215)]
        
        # Moon position drifts slowly
        moon_x = 0.3 + 0.4 * math.sin(phase * 0.1 * math.pi)
        moon_y = 0.2 + 0.1 * math.cos(phase * 0.08 * math.pi)
        
        # === PIXELS: Moonlit scene ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Distance from moon
            moon_dist = ((nx - moon_x) ** 2 + (ny - moon_y) ** 2) ** 0.5
            
            # Moon glow
            glow = math.exp(-moon_dist * 3) * 0.5
            
            # Ambient moonlight
            ambient = 0.25 + (1 - ny) * 0.1
            
            brightness = ambient + glow
            color_pos = (nx * 0.2 + phase * 0.03) % 1.0
            r, g, b = self._interpolate_palette_color(moon_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Gentle drift like moonbeams ===
        for i, fixture in enumerate(cats['movers']):
            drift_x = math.sin((phase * 0.08 + i * 0.5) * math.pi) * 20
            drift_y = math.cos((phase * 0.06 + i * 0.4) * math.pi) * 10
            
            color_pos = (i * 0.15 + phase * 0.04) % 1.0
            r, g, b = self._interpolate_palette_color(moon_palette, color_pos)
            
            self._apply_mover_position(fixture, drift_x, 35 + drift_y, r, g, b,
                                       intensity_scale * 0.5,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Soft ambient ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase * 0.05 + i * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(moon_palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 40), skip_pan_tilt=True)
    
    def _apply_ensemble_dreamy(self, fixtures: list, effect: EffectParameters, phase: float):
        """Dreamy - soft pastels, slow morphing, ethereal."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['pastel']
        
        # Very slow morphing
        morph = math.sin(phase * 0.3 * math.pi)
        
        # === PIXELS: Soft morphing clouds ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Soft blobs
            blob1 = math.sin((nx * 2 + phase * 0.15) * math.pi) * math.cos((ny * 2 + phase * 0.1) * math.pi)
            blob2 = math.cos((nx * 1.5 - phase * 0.12) * math.pi) * math.sin((ny * 1.5 + phase * 0.08) * math.pi)
            
            blend = (blob1 + blob2 + 2) / 4
            
            brightness = 0.5 + blend * 0.4
            color_pos = (blend + phase * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Float dreamily ===
        for i, fixture in enumerate(cats['movers']):
            float_x = math.sin((phase * 0.1 + i * 0.5) * math.pi) * 25
            float_y = math.cos((phase * 0.08 + i * 0.4) * math.pi) * 15
            
            color_pos = (i * 0.2 + phase * 0.06) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, float_x, 35 + float_y, r, g, b,
                                       intensity_scale * (0.5 + morph * 0.2),
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Soft dreamy glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase * 0.06 + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            brightness = 0.4 + 0.15 * math.sin((phase * 0.5 + i * 0.3) * math.pi)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_matrix(self, fixtures: list, effect: EffectParameters, phase: float):
        """Matrix - falling green code."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # === PIXELS: Falling code ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Multiple falling streams
            stream_speed = 1.2 + (i % 7) * 0.2
            stream_phase = (ny + phase * stream_speed + i * 0.1) % 1.0
            
            # Lead character (bright), trail (fading)
            if stream_phase < 0.1:
                brightness = 1.0 - stream_phase / 0.1
                g = 255
                r = int(200 * brightness)  # White lead
            elif stream_phase < 0.4:
                brightness = 0.6 * (1 - (stream_phase - 0.1) / 0.3)
                g = int(255 * brightness)
                r = 0
            else:
                brightness = 0.1
                g = int(50 * brightness)
                r = 0
            
            b = 0
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale)
        
        # === MOVERS: Scan down ===
        for i, fixture in enumerate(cats['movers']):
            scan_phase = (phase * 0.5 + i * 0.2) % 1.0
            
            pan = math.sin((phase * 0.2 + i * 0.4) * math.pi) * 30
            tilt = 20 + scan_phase * 40  # Scan downward
            
            self._apply_mover_position(fixture, pan, tilt, 50, 255, 50,
                                       intensity_scale * 0.8,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Green ambient ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            flicker = 0.4 + 0.3 * math.sin((phase * 5 + i * 2) * math.pi)
            self.apply_static([fixture], "#00ff00",
                            int(flicker * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_inferno(self, fixtures: list, effect: EffectParameters, phase: float):
        """Inferno - intense fire with dancing flames."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['fire']
        
        # === PIXELS: Intense flames ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Dancing flames
            flame = math.sin((nx * 8 + phase * 3 + i * 0.2) * math.pi) * 0.2
            flame += math.sin((ny * 6 - phase * 2.5) * math.pi) * 0.15
            flame += math.sin((nx * 4 + ny * 4 + phase * 4) * math.pi) * 0.1
            
            # Hotter at bottom
            heat = (1 - ny) * 0.5 + 0.3
            
            brightness = heat + flame
            color_pos = (heat + flame * 2 + phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * min(1.0, brightness))
        
        # === MOVERS: Wild flame movement ===
        for i, fixture in enumerate(cats['movers']):
            wild_x = math.sin((phase * 2 + i * 0.5) * math.pi) * 40
            wild_x += math.sin((phase * 5 + i * 0.3) * math.pi) * 15
            wild_y = math.cos((phase * 3 + i * 0.4) * math.pi) * 20
            
            color_pos = (i * 0.2 + phase * 0.25) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, wild_x, 30 + wild_y, r, g, b,
                                       intensity_scale * 0.95,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Intense fire glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase * 0.3 + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            flicker = 0.7 + 0.3 * math.sin((phase * 8 + i * 2) * math.pi)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(flicker * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_arctic(self, fixtures: list, effect: EffectParameters, phase: float):
        """Arctic - cold icy blues with northern lights hints."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Cold colors with aurora hints
        arctic_palette = [(180, 220, 255), (150, 200, 240), (200, 240, 255), (100, 180, 220), (120, 255, 200)]
        
        # === PIXELS: Ice and aurora ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Ice shimmer
            shimmer = math.sin((nx * 10 + phase * 0.5) * math.pi) * 0.1
            shimmer += math.cos((ny * 8 + phase * 0.3) * math.pi) * 0.08
            
            # Aurora at top
            aurora = 0
            if ny < 0.4:
                aurora = (0.4 - ny) * math.sin((nx * 5 + phase * 0.8) * math.pi) * 0.3
            
            brightness = 0.5 + shimmer + max(0, aurora)
            color_pos = (nx * 0.2 + aurora * 2 + phase * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(arctic_palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Slow cold movement ===
        for i, fixture in enumerate(cats['movers']):
            drift = math.sin((phase * 0.1 + i * 0.5) * math.pi) * 25
            tilt_drift = math.cos((phase * 0.08 + i * 0.4) * math.pi) * 12
            
            color_pos = (i * 0.2 + phase * 0.06) % 1.0
            r, g, b = self._interpolate_palette_color(arctic_palette, color_pos)
            
            self._apply_mover_position(fixture, drift, 35 + tilt_drift, r, g, b,
                                       intensity_scale * 0.65,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Cold ambient ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase * 0.08 + i * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(arctic_palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 55), skip_pan_tilt=True)
    
    def _apply_ensemble_dance_floor(self, fixtures: list, effect: EffectParameters, phase: float):
        """Dance floor - classic disco patterns, movers sweeping."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Disco colors
        disco_palette = [(255, 0, 100), (0, 255, 200), (255, 200, 0), (200, 0, 255), (0, 150, 255)]
        
        # Beat simulation
        beat = abs(math.sin(phase * 4 * math.pi))
        
        # === PIXELS: Dance floor tiles ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Tile pattern
            tile_x = int(nx * 4) % 2
            tile_y = int(ny * 4 + phase) % 2
            tile = (tile_x + tile_y) % 2
            
            # Chase across tiles
            chase = (nx + phase * 2) % 1.0
            color_idx = int(chase * len(disco_palette)) % len(disco_palette)
            r, g, b = disco_palette[color_idx]
            
            brightness = 0.5 + tile * 0.3 + beat * 0.2
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Classic disco sweep ===
        for i, fixture in enumerate(cats['movers']):
            sweep = math.sin((phase * 1.5 + i * 0.3) * 2 * math.pi) * 55
            tilt = 40 + beat * 10
            
            color_idx = int((phase * 2 + i) % len(disco_palette))
            r, g, b = disco_palette[color_idx]
            
            self._apply_mover_position(fixture, sweep, tilt, r, g, b,
                                       intensity_scale * (0.7 + beat * 0.3),
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Beat flash ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_idx = int((phase * 1.5 + i * 0.5) % len(disco_palette))
            r, g, b = disco_palette[color_idx]
            brightness = 0.5 + beat * 0.4
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_gentle_waves(self, fixtures: list, effect: EffectParameters, phase: float):
        """Gentle waves - very calm, slow rolling waves of light."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ocean']
        
        # === PIXELS: Slow rolling waves ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Very gentle waves
            wave1 = math.sin((nx * 2 - phase * 0.3) * math.pi) * 0.15
            wave2 = math.sin((ny * 1.5 + phase * 0.2) * math.pi) * 0.1
            
            brightness = 0.5 + wave1 + wave2
            color_pos = (nx * 0.3 + phase * 0.05) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Gentle rocking ===
        for i, fixture in enumerate(cats['movers']):
            rock_x = math.sin((phase * 0.15 + i * 0.4) * math.pi) * 15
            rock_y = math.cos((phase * 0.1 + i * 0.3) * math.pi) * 8
            
            color_pos = (i * 0.15 + phase * 0.06) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_mover_position(fixture, rock_x, 35 + rock_y, r, g, b,
                                       intensity_scale * 0.55,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Soft ocean glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_pos = (phase * 0.06 + i * 0.12) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            brightness = 0.4 + 0.1 * math.sin((phase * 0.3 + i * 0.2) * math.pi)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(brightness * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_enchanted(self, fixtures: list, effect: EffectParameters, phase: float):
        """Enchanted forest - magical sparkles and fairy lights."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        
        # Magical colors
        magic_palette = [(150, 100, 255), (100, 255, 150), (255, 150, 200), (200, 255, 100), (100, 200, 255)]
        
        # === PIXELS: Sparkles and fairy dust ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for i, pixel in enumerate(all_pixels):
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Base forest green
            base_r, base_g, base_b = 30, 80, 50
            
            # Sparkles (random-ish based on phase and position)
            sparkle_phase = (phase * 5 + i * 0.618) % 1.0
            is_sparkle = sparkle_phase < 0.05
            
            if is_sparkle:
                color_idx = i % len(magic_palette)
                r, g, b = magic_palette[color_idx]
                brightness = 1.0 - sparkle_phase / 0.05
            else:
                # Gentle forest glow
                glow = 0.3 + 0.2 * math.sin((nx * 3 + phase * 0.2) * math.pi)
                r = int(base_r + glow * 30)
                g = int(base_g + glow * 50)
                b = int(base_b + glow * 30)
                brightness = 1.0
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Float like fairies ===
        for i, fixture in enumerate(cats['movers']):
            float_x = math.sin((phase * 0.3 + i * 0.6) * math.pi) * 30
            float_x += math.sin((phase * 0.8 + i * 0.4) * math.pi) * 10
            float_y = math.cos((phase * 0.25 + i * 0.5) * math.pi) * 15
            
            color_idx = int((phase * 2 + i) % len(magic_palette))
            r, g, b = magic_palette[color_idx]
            
            self._apply_mover_position(fixture, float_x, 30 + float_y, r, g, b,
                                       intensity_scale * 0.75,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Magical glow ===
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            color_idx = int((phase * 0.5 + i) % len(magic_palette))
            r, g, b = magic_palette[color_idx]
            sparkle = 0.4 + 0.3 * max(0, math.sin((phase * 4 + i * 1.5) * math.pi))
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(sparkle * intensity_scale * 100), skip_pan_tilt=True)
    
    def _apply_ensemble_slow_chase(self, fixtures: list, effect: EffectParameters, phase: float):
        """Slow chase - gentle color chase across all fixtures."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['rainbow']
        
        # === PIXELS: Slow color chase ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        total_pixels = len(all_pixels)
        for i, pixel in enumerate(all_pixels):
            pos = i / max(1, total_pixels - 1)
            color_pos = (pos - phase * 0.5) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * 0.75)
        
        # === MOVERS: Follow the chase ===
        num_movers = len(cats['movers'])
        for i, fixture in enumerate(cats['movers']):
            mover_pos = i / max(1, num_movers - 1)
            color_pos = (mover_pos - phase * 0.5) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            
            # Gentle sway
            pan = math.sin((phase * 0.2 + i * 0.4) * math.pi) * 20
            tilt = 35
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Chase colors ===
        total_wash = len(cats['wash'] + cats['other'])
        for i, fixture in enumerate(cats['wash'] + cats['other']):
            wash_pos = i / max(1, total_wash - 1)
            color_pos = (wash_pos - phase * 0.5) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 65), skip_pan_tilt=True)
    
    def _apply_ensemble_color_wash(self, fixtures: list, effect: EffectParameters, phase: float):
        """Color wash - single color slowly morphing across all."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['rainbow']
        
        # All fixtures same color, slowly changing
        color_pos = phase * 0.2 % 1.0
        r, g, b = self._interpolate_palette_color(palette, color_pos)
        
        # === PIXELS: Unified color ===
        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            
            # Slight variation
            var = math.sin((nx + ny + phase * 0.3) * math.pi) * 0.1
            brightness = 0.7 + var
            
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)
        
        # === MOVERS: Same color, gentle movement ===
        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.1 + i * 0.5) * math.pi) * 20
            tilt = 35 + math.cos((phase * 0.08 + i * 0.4) * math.pi) * 10
            
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)
        
        # === WASH: Same color ===
        for fixture in cats['wash'] + cats['other']:
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 70), skip_pan_tilt=True)
    
    # ==================== NEW ENSEMBLE EFFECTS (batch 2) ====================

    def _apply_ensemble_solar_flare(self, fixtures: list, effect: EffectParameters, phase: float):
        """Solar flare - intense burst radiating from center, corona glow."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['fire']
        tau = 2 * math.pi
        burst = max(0, math.sin(phase * tau * 2)) ** 3

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dx, dy = nx - 0.5, ny - 0.5
            dist = (dx*dx + dy*dy) ** 0.5
            corona = max(0, 1.0 - dist * 3) * 0.6
            flare_ray = abs(math.sin(math.atan2(dy, dx) * 6 + phase * tau)) * max(0, 0.4 - dist) * burst
            brightness = min(1.0, corona + flare_ray + burst * 0.3 * max(0, 1.0 - dist * 2))
            color_pos = (dist * 2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            angle = (phase + i * 0.3) * tau
            pan = math.sin(angle) * 40 * burst
            tilt = 30 + math.cos(angle * 0.7) * 20 * burst
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * (0.3 + burst * 0.7),
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, phase % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * (30 + burst * 70)), skip_pan_tilt=True)

    def _apply_ensemble_snowfall(self, fixtures: list, effect: EffectParameters, phase: float):
        """Snowfall - gentle white flakes drifting down with cold blue ambient."""
        import math, random
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ice']
        tau = 2 * math.pi
        rand = random.Random(42)

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        num_flakes = 12
        flakes = []
        for f in range(num_flakes):
            fx = rand.random()
            fy = (phase * (0.3 + f * 0.04) + f * 0.08) % 1.2 - 0.1
            drift = math.sin((phase * 2 + f) * tau) * 0.05
            flakes.append((fx + drift, fy, 0.04 + rand.random() * 0.03))
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            brightness = 0.15
            for fx, fy, sz in flakes:
                dist = ((nx - fx) ** 2 + (ny - fy) ** 2) ** 0.5
                if dist < sz:
                    brightness = max(brightness, (1.0 - dist / sz) * 0.9)
            color_pos = (ny * 0.3 + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.3 + i) * tau) * 25
            tilt = 40 + math.sin((phase * 0.2 + i * 0.5) * tau) * 15
            r, g, b = 200, 210, 230
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.5,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.1) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 40), skip_pan_tilt=True)

    def _apply_ensemble_electric_storm(self, fixtures: list, effect: EffectParameters, phase: float):
        """Electric storm - lightning bolts flash while purple clouds roll."""
        import math, random
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['galaxy']
        tau = 2 * math.pi
        bolt_seed = int(phase * 8) 
        rand = random.Random(bolt_seed)
        flash = 1.0 if rand.random() < 0.25 else 0.0

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        bolt_x = rand.random()
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            cloud = 0.2 + 0.15 * math.sin((nx * 3 + phase) * tau) * math.sin((ny * 2 - phase * 0.5) * tau)
            bolt_dist = abs(nx - bolt_x)
            lightning = flash * max(0, 1.0 - bolt_dist * 8) * max(0, 1.0 - ny * 0.5)
            brightness = min(1.0, cloud + lightning)
            if lightning > 0.3:
                r, g, b = 220, 220, 255
            else:
                color_pos = (nx * 0.5 + phase * 0.3) % 1.0
                r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            jolt = flash * 30
            pan = math.sin((phase + i * 0.4) * tau) * 20 + jolt * (rand.random() - 0.5)
            tilt = 30 + math.sin((phase * 0.5 + i) * tau) * 15
            brightness = 0.4 + flash * 0.6
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.1) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * brightness,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            brightness = 30 + int(flash * 70)
            r, g, b = self._interpolate_palette_color(palette, phase % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * brightness), skip_pan_tilt=True)

    def _apply_ensemble_fairy_dust(self, fixtures: list, effect: EffectParameters, phase: float):
        """Fairy dust - twinkling sparkles drift across the stage in pastel colors."""
        import math, random
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['pastel']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        rand = random.Random(42)
        sparkles = [(rand.random(), rand.random(), rand.random() * 0.618) for _ in range(20)]
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            brightness = 0.08
            for sx, sy, spd in sparkles:
                sx_moving = (sx + phase * (0.1 + spd * 0.15)) % 1.0
                sy_moving = (sy + phase * (0.05 + spd * 0.08)) % 1.0
                dist = ((nx - sx_moving)**2 + (ny - sy_moving)**2) ** 0.5
                twinkle = (math.sin((phase * 8 + spd * 20) * tau) + 1) / 2
                if dist < 0.05:
                    brightness = max(brightness, (1.0 - dist / 0.05) * twinkle)
            color_pos = (nx * 0.3 + ny * 0.3 + phase * 0.5) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.5 + i * 0.618) * tau) * 35
            tilt = 30 + math.sin((phase * 0.3 + i) * tau) * 20
            color_pos = (phase + i * 0.25) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            twinkle = (math.sin((phase * 6 + i * 2) * tau) + 1) / 2
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * (0.3 + twinkle * 0.5),
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            color_pos = (phase * 0.4) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 40), skip_pan_tilt=True)

    def _apply_ensemble_cyberpunk(self, fixtures: list, effect: EffectParameters, phase: float):
        """Cyberpunk - harsh neon bars scan with glitch effects."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['neon']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        scan_y = (phase * 2) % 1.0
        glitch = abs(math.sin(phase * 17 * tau)) > 0.92
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            bar_dist = abs(ny - scan_y)
            brightness = max(0, 1.0 - bar_dist * 6) * 0.8
            grid = 0.15 if (int(nx * 10) + int(ny * 10)) % 2 == 0 else 0.05
            brightness = max(brightness, grid)
            if glitch:
                brightness = min(1.0, brightness + 0.5)
            color_pos = (nx * 0.5 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = (math.sin(phase * tau * 3) * 60) if not glitch else (70 * (-1 if i % 2 == 0 else 1))
            tilt = 25 + abs(math.sin(phase * tau * 2)) * 30
            r, g, b = self._interpolate_palette_color(palette, (phase * 2 + i * 0.3) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.8,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.5) % 1.0)
            brt = 60 + (40 if glitch else 0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * brt), skip_pan_tilt=True)

    def _apply_ensemble_desert_mirage(self, fixtures: list, effect: EffectParameters, phase: float):
        """Desert mirage - warm heat shimmer with sandy earth tones."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['earth']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            shimmer = math.sin((nx * 8 + phase * 3) * tau) * 0.1 * math.sin((ny * 6 - phase * 2) * tau)
            heat_wave = 0.5 + 0.3 * math.sin((nx * 2 + phase) * tau)
            horizon = max(0, 1.0 - abs(ny - 0.6) * 3) * 0.4
            brightness = min(1.0, heat_wave + shimmer + horizon)
            color_pos = (nx * 0.3 + ny * 0.5 + phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.4 + i * 0.5) * tau) * 30
            tilt = 35 + math.sin((phase * 0.3 + i * 0.3) * tau) * 10
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.6,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.15) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 50), skip_pan_tilt=True)

    def _apply_ensemble_cherry_blossom(self, fixtures: list, effect: EffectParameters, phase: float):
        """Cherry blossom - pink petals drifting down through warm light."""
        import math, random
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['candy']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        rand = random.Random(42)
        petals = [(rand.random(), rand.random(), rand.random() * 0.3) for _ in range(15)]
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            brightness = 0.2 + 0.1 * math.sin((nx * 3 + phase) * tau)
            for px, drift, speed in petals:
                py = (phase * (0.2 + speed) + drift * 3) % 1.3 - 0.15
                petal_x = px + math.sin((py * 4 + drift * 10) * tau) * 0.08
                dist = ((nx - petal_x)**2 + (ny - py)**2) ** 0.5
                if dist < 0.04:
                    brightness = max(brightness, (1.0 - dist / 0.04) * 0.85)
            color_pos = (nx * 0.2 + phase * 0.3) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.4 + i * 0.618) * tau) * 25
            tilt = 35 + math.sin((phase * 0.3 + i) * tau) * 15
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.15) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.6,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.2) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 45), skip_pan_tilt=True)

    def _apply_ensemble_deep_space(self, fixtures: list, effect: EffectParameters, phase: float):
        """Deep space - slow rotating nebula with distant twinkling stars."""
        import math, random
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['galaxy']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        rand = random.Random(99)
        stars = [(rand.random(), rand.random(), rand.random()) for _ in range(25)]
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dx, dy = nx - 0.5, ny - 0.5
            angle = math.atan2(dy, dx) + phase * 0.3
            dist = (dx*dx + dy*dy) ** 0.5
            nebula = 0.25 + 0.2 * math.sin(angle * 3) * math.sin(dist * 8 - phase * tau)
            star_brightness = 0.0
            for sx, sy, sp in stars:
                sd = ((nx - sx)**2 + (ny - sy)**2) ** 0.5
                if sd < 0.015:
                    twinkle = (math.sin((phase * 6 + sp * 20) * tau) + 1) / 2
                    star_brightness = max(star_brightness, twinkle * (1.0 - sd / 0.015))
            brightness = min(1.0, nebula + star_brightness)
            color_pos = (angle / tau + phase * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            if star_brightness > 0.5:
                r, g, b = 230, 230, 255
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.2 + i * 0.5) * tau) * 40
            tilt = 20 + math.sin((phase * 0.15 + i * 0.3) * tau) * 25
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.3) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.5,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.1) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 30), skip_pan_tilt=True)

    def _apply_ensemble_rave(self, fixtures: list, effect: EffectParameters, phase: float):
        """Rave - fast strobing sections with alternating neon colors."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['neon']
        tau = 2 * math.pi
        beat = int(phase * 8) % 4

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            zone = int(nx * 4) % 4
            on = 1.0 if zone == beat else 0.0
            flash = abs(math.sin(phase * tau * 8))
            brightness = on * (0.5 + flash * 0.5)
            color_pos = (zone * 0.25 + phase * 0.5) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            angle = (beat * 90) + (i * 45)
            pan = math.sin(math.radians(angle)) * 60
            tilt = 20 + abs(math.sin(phase * tau * 4)) * 30
            r, g, b = self._interpolate_palette_color(palette, (beat * 0.25 + i * 0.1) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.9,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (beat * 0.25) % 1.0)
            on = 80 if int(phase * 8) % 2 == 0 else 20
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * on), skip_pan_tilt=True)

    def _apply_ensemble_vortex(self, fixtures: list, effect: EffectParameters, phase: float):
        """Vortex - swirling spiral pulling everything toward center."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['aurora']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dx, dy = nx - 0.5, ny - 0.5
            dist = (dx*dx + dy*dy) ** 0.5
            angle = math.atan2(dy, dx)
            spiral = math.sin((angle * 3 - dist * 12 + phase * 4) * math.pi)
            brightness = max(0.05, (spiral + 1) / 2 * (1.0 - dist * 0.8))
            color_pos = (angle / tau + dist * 2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            angle = phase * tau * 1.5 + i * tau / max(1, len(cats['movers']))
            radius = 0.3 + 0.15 * math.sin(phase * tau * 0.5)
            pan = math.sin(angle) * 50 * radius
            tilt = 25 + math.cos(angle) * 25 * radius
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            color_pos = (phase * 0.6) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 50), skip_pan_tilt=True)

    def _apply_ensemble_golden_hour(self, fixtures: list, effect: EffectParameters, phase: float):
        """Golden hour - warm amber sun low on horizon with long shadows."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        tau = 2 * math.pi
        palette = self.GRADIENT_PALETTES['sunset']

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        sun_x = 0.5 + 0.3 * math.sin(phase * tau * 0.3)
        sun_y = 0.75
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dist = ((nx - sun_x)**2 + (ny - sun_y)**2) ** 0.5
            glow = max(0, 1.0 - dist * 2.5)
            horizon_warm = max(0, 1.0 - abs(ny - 0.7) * 3) * 0.4
            brightness = min(1.0, glow * 0.7 + horizon_warm + 0.15)
            color_pos = (dist * 0.5 + phase * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.2 + i * 0.5) * tau) * 20
            tilt = 40 + math.sin((phase * 0.15 + i * 0.3) * tau) * 10
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.1) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.65,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.1) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 55), skip_pan_tilt=True)

    def _apply_ensemble_tidal_wave(self, fixtures: list, effect: EffectParameters, phase: float):
        """Tidal wave - massive wave builds and crashes across the stage."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ocean']
        tau = 2 * math.pi

        wave_x = (phase * 1.5) % 1.5 - 0.25
        wave_width = 0.15
        wall_height = min(1.0, max(0, wave_x * 1.5))

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            wave_dist = abs(nx - wave_x)
            foam = max(0, 1.0 - wave_dist / wave_width) * wall_height
            wake = max(0, 0.3 - abs(nx - (wave_x - 0.2)) * 3) * (1.0 - ny * 0.5) if nx < wave_x else 0
            deep = 0.15 + 0.1 * math.sin((nx * 4 + phase) * tau)
            brightness = min(1.0, foam + wake + deep)
            color_pos = (wave_dist * 2 + phase * 0.3) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            if foam > 0.6:
                r, g, b = min(255, r + 80), min(255, g + 80), min(255, b + 40)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = (wave_x - 0.5) * 100
            tilt = 20 + wall_height * 30
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * (0.3 + wall_height * 0.6),
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.3) % 1.0)
            brt = 30 + int(wall_height * 50)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * brt), skip_pan_tilt=True)

    def _apply_ensemble_northern_forest(self, fixtures: list, effect: EffectParameters, phase: float):
        """Northern forest - deep greens with shafts of light through canopy."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['forest']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        num_shafts = 4
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            base_green = 0.25 + 0.1 * math.sin((nx * 5 + ny * 3 + phase) * tau)
            shaft_brightness = 0.0
            for s in range(num_shafts):
                shaft_x = (0.15 + s * 0.25 + math.sin((phase * 0.3 + s) * tau) * 0.05)
                shaft_dist = abs(nx - shaft_x)
                if shaft_dist < 0.04:
                    shaft_brightness = max(shaft_brightness, (1.0 - shaft_dist / 0.04) * 0.7 * (1.0 - ny * 0.3))
            brightness = min(1.0, base_green + shaft_brightness)
            color_pos = (ny * 0.5 + phase * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            if shaft_brightness > 0.3:
                r = min(255, r + 60)
                g = min(255, g + 40)
                b = min(255, b + 10)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.3 + i * 0.618) * tau) * 20
            tilt = 45 + math.sin((phase * 0.2 + i * 0.5) * tau) * 10
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.5,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.1) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 40), skip_pan_tilt=True)

    def _apply_ensemble_thunder_roll(self, fixtures: list, effect: EffectParameters, phase: float):
        """Thunder roll - low rumbling flashes that sweep across the stage."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['midnight']
        tau = 2 * math.pi

        roll_x = (phase * 2) % 1.5 - 0.25
        roll_width = 0.3
        flash_intensity = max(0, math.sin(phase * tau * 6)) ** 4

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            roll_dist = abs(nx - roll_x)
            roll_glow = max(0, 1.0 - roll_dist / roll_width) * flash_intensity * 0.8
            ambient = 0.12 + 0.05 * math.sin((nx * 3 + phase) * tau)
            brightness = min(1.0, ambient + roll_glow)
            if roll_glow > 0.3:
                r, g, b = 200, 200, 230
            else:
                color_pos = (nx * 0.4 + phase * 0.2) % 1.0
                r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = (roll_x - 0.5) * 80
            tilt = 30 + flash_intensity * 20
            brightness = 0.3 + flash_intensity * 0.6
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.1) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * brightness,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, phase % 1.0)
            brt = 15 + int(flash_intensity * 60)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * brt), skip_pan_tilt=True)

    def _apply_ensemble_prism(self, fixtures: list, effect: EffectParameters, phase: float):
        """Prism - white light splits into rainbow bands that shift and rotate."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['rainbow']
        tau = 2 * math.pi

        rotation = phase * math.pi * 0.5
        cos_r, sin_r = math.cos(rotation), math.sin(rotation)

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dx, dy = nx - 0.5, ny - 0.5
            rx = dx * cos_r + dy * sin_r
            band_pos = (rx + 0.5 + phase * 0.3) % 1.0
            center_dist = (dx*dx + dy*dy) ** 0.5
            brightness = max(0.1, 0.8 - center_dist * 0.6)
            r, g, b = self._interpolate_palette_color(palette, band_pos)
            if center_dist < 0.05:
                r, g, b = 240, 240, 240
                brightness = 0.9
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.5 + i * 0.618) * tau) * 35
            tilt = 30 + math.cos((phase * 0.4 + i * 0.5) * tau) * 15
            hue = (phase + i * 0.15) % 1.0
            r, g, b = self._interpolate_palette_color(palette, hue)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)

        for i, fixture in enumerate(cats['wash'] + cats['other']):
            hue = (phase * 0.3 + i * 0.1) % 1.0
            r, g, b = self._interpolate_palette_color(palette, hue)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 55), skip_pan_tilt=True)

    def _apply_ensemble_campfire(self, fixtures: list, effect: EffectParameters, phase: float):
        """Campfire - flickering orange-yellow center with dim warm surround."""
        import math, random
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['fire']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        rand = random.Random(int(phase * 20))
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dx, dy = nx - 0.5, ny - 0.65
            dist = (dx*dx + dy*dy) ** 0.5
            flame = max(0, 1.0 - dist * 3.5)
            flicker = 0.7 + rand.random() * 0.3
            flame *= flicker
            ember = max(0, 0.2 - dist) * 2 * abs(math.sin(phase * tau * 3 + nx * 10))
            brightness = min(1.0, flame + ember)
            color_pos = (dist * 2 + phase * 0.5) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.5 + i) * tau) * 15
            tilt = 40 + math.sin((phase * 0.8 + i * 0.5) * tau) * 8
            flicker = 0.5 + rand.random() * 0.4
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * flicker,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.2) % 1.0)
            flicker = 35 + int(rand.random() * 20)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * flicker), skip_pan_tilt=True)

    def _apply_ensemble_moonrise(self, fixtures: list, effect: EffectParameters, phase: float):
        """Moonrise - silver disc rises slowly with blue twilight ambiance."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['midnight']
        tau = 2 * math.pi

        moon_x = 0.5 + 0.1 * math.sin(phase * tau * 0.2)
        moon_y = 1.0 - phase % 1.0 * 0.8
        moon_radius = 0.1

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dist = ((nx - moon_x)**2 + (ny - moon_y)**2) ** 0.5
            if dist < moon_radius:
                brightness = 0.9
                r, g, b = 220, 225, 240
            elif dist < moon_radius + 0.1:
                glow = (1.0 - (dist - moon_radius) / 0.1)
                brightness = glow * 0.4
                r, g, b = 180, 190, 220
            else:
                color_pos = (ny * 0.5 + phase * 0.1) % 1.0
                r, g, b = self._interpolate_palette_color(palette, color_pos)
                brightness = 0.15 + 0.05 * math.sin((nx * 4 + phase) * tau)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = (moon_x - 0.5) * 60
            tilt = 15 + (1.0 - moon_y) * 40
            self._apply_mover_position(fixture, pan, tilt, 200, 210, 230,
                                       intensity_scale * 0.5,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.1) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 30), skip_pan_tilt=True)

    def _apply_ensemble_pulse_wave(self, fixtures: list, effect: EffectParameters, phase: float):
        """Pulse wave - concentric rings expand from center with color shift."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['tropical']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dx, dy = nx - 0.5, ny - 0.5
            dist = (dx*dx + dy*dy) ** 0.5
            ring = math.sin((dist * 8 - phase * 4) * math.pi)
            brightness = max(0.05, (ring + 1) / 2)
            color_pos = (dist * 2 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pulse = (math.sin(phase * tau * 2) + 1) / 2
            pan = math.sin((phase + i * 0.5) * tau) * 30 * pulse
            tilt = 30 + pulse * 20
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * (0.4 + pulse * 0.5),
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            pulse = (math.sin(phase * tau * 2) + 1) / 2
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.5) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * (30 + pulse * 40)), skip_pan_tilt=True)

    def _apply_ensemble_laser_grid(self, fixtures: list, effect: EffectParameters, phase: float):
        """Laser grid - crossing laser lines create a sci-fi grid pattern."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['neon']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        grid_shift = phase * 0.3
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            h_line = abs(math.sin((ny * 6 + grid_shift) * math.pi))
            v_line = abs(math.sin((nx * 6 + grid_shift) * math.pi))
            h_beam = max(0, 1.0 - h_line * 4) * 0.8
            v_beam = max(0, 1.0 - v_line * 4) * 0.8
            brightness = min(1.0, max(h_beam, v_beam))
            node = min(h_line, v_line)
            if node < 0.08:
                brightness = 1.0
            color_pos = (nx * 0.5 + ny * 0.5 + phase) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase + i * 0.4) * tau) * 45
            tilt = 25 + math.sin((phase * 2 + i * 0.3) * tau) * 20
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.8 + i * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.4) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 30), skip_pan_tilt=True)

    def _apply_ensemble_haunted(self, fixtures: list, effect: EffectParameters, phase: float):
        """Haunted - eerie flickering with ghostly movement and cold palette."""
        import math, random
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ice']
        tau = 2 * math.pi

        rand = random.Random(int(phase * 12))
        ghost_x = 0.5 + 0.35 * math.sin(phase * tau * 0.4)
        ghost_y = 0.5 + 0.25 * math.cos(phase * tau * 0.3)

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dist = ((nx - ghost_x)**2 + (ny - ghost_y)**2) ** 0.5
            ghost_glow = max(0, 0.7 - dist * 3)
            flicker = 0.05 + rand.random() * 0.1
            brightness = min(1.0, ghost_glow + flicker)
            color_pos = (dist + phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            r = max(0, r - 40)
            g = int(g * 0.7)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = (ghost_x - 0.5) * 80 + rand.random() * 10 - 5
            tilt = 30 + (ghost_y - 0.5) * 30
            self._apply_mover_position(fixture, pan, tilt, 150, 180, 200,
                                       intensity_scale * (0.2 + rand.random() * 0.3),
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            flicker = 10 + int(rand.random() * 20)
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.1) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * flicker), skip_pan_tilt=True)

    def _apply_ensemble_color_bounce(self, fixtures: list, effect: EffectParameters, phase: float):
        """Color bounce - bright orbs bounce off walls with color trails."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['rainbow']
        tau = 2 * math.pi

        orbs = []
        for o in range(3):
            bx = abs(math.sin((phase * (1.2 + o * 0.3) + o * 0.5) * math.pi))
            by = abs(math.sin((phase * (0.8 + o * 0.4) + o * 0.7) * math.pi))
            orbs.append((bx, by, o * 0.33))

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            brightness = 0.05
            best_hue = 0.0
            for bx, by, hue in orbs:
                dist = ((nx - bx)**2 + (ny - by)**2) ** 0.5
                if dist < 0.15:
                    b_val = (1.0 - dist / 0.15) ** 0.7
                    if b_val > brightness:
                        brightness = b_val
                        best_hue = hue
            color_pos = (best_hue + phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            o = i % len(orbs)
            pan = (orbs[o][0] - 0.5) * 80
            tilt = 20 + orbs[o][1] * 40
            r, g, b = self._interpolate_palette_color(palette, (orbs[o][2] + phase * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.3) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 35), skip_pan_tilt=True)

    def _apply_ensemble_silk_curtain(self, fixtures: list, effect: EffectParameters, phase: float):
        """Silk curtain - flowing fabric waves in rich warm colors."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['sunset']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            fold1 = math.sin((nx * 5 + phase * 2) * tau) * 0.3
            fold2 = math.sin((nx * 3 - phase * 1.5 + ny * 2) * tau) * 0.2
            fabric = 0.5 + fold1 + fold2
            drape = 1.0 - ny * 0.3
            brightness = min(1.0, max(0.15, fabric * drape))
            color_pos = (nx * 0.4 + fold1 + phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.5 + i * 0.618) * tau) * 25
            tilt = 35 + math.sin((phase * 0.3 + i * 0.4) * tau) * 12
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.15) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.6,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.15) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 50), skip_pan_tilt=True)

    def _apply_ensemble_crystal_cave(self, fixtures: list, effect: EffectParameters, phase: float):
        """Crystal cave - sparkling reflections from faceted surfaces."""
        import math, random
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['ice']
        tau = 2 * math.pi

        rand = random.Random(42)
        crystals = [(rand.random(), rand.random(), rand.random()) for _ in range(18)]

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            brightness = 0.12
            for cx, cy, spd in crystals:
                dist = ((nx - cx)**2 + (ny - cy)**2) ** 0.5
                if dist < 0.06:
                    sparkle = (math.sin((phase * 5 + spd * 15) * tau) + 1) / 2
                    b_val = (1.0 - dist / 0.06) * sparkle * 0.9
                    brightness = max(brightness, b_val)
            color_pos = (nx * 0.3 + ny * 0.3 + phase * 0.2) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            if brightness > 0.6:
                r = min(255, r + 50)
                g = min(255, g + 50)
                b = min(255, b + 30)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.4 + i * 0.5) * tau) * 30
            tilt = 25 + math.sin((phase * 0.5 + i * 0.3) * tau) * 20
            sparkle = (math.sin((phase * 4 + i * 3) * tau) + 1) / 2
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * (0.3 + sparkle * 0.5),
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.15) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 35), skip_pan_tilt=True)

    def _apply_ensemble_neon_rain(self, fixtures: list, effect: EffectParameters, phase: float):
        """Neon rain - bright vertical streaks fall through dark cityscape."""
        import math, random
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['neon']
        tau = 2 * math.pi

        rand = random.Random(42)
        streaks = [(rand.random(), rand.random() * 0.5, 0.5 + rand.random() * 0.8) for _ in range(12)]

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            brightness = 0.05
            for sx, offset, speed in streaks:
                streak_y = (phase * speed + offset) % 1.3 - 0.15
                x_dist = abs(nx - sx)
                y_dist = ny - streak_y
                if x_dist < 0.025 and 0 < y_dist < 0.15:
                    b_val = (1.0 - y_dist / 0.15) * (1.0 - x_dist / 0.025) * 0.9
                    brightness = max(brightness, b_val)
                if x_dist < 0.015 and abs(ny - streak_y) < 0.02:
                    brightness = max(brightness, 1.0)
            color_pos = (nx + phase * 0.3) % 1.0
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.6 + i * 0.5) * tau) * 35
            tilt = 20 + abs(math.sin(phase * tau * 2)) * 25
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.3) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.6,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.4) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 25), skip_pan_tilt=True)

    def _apply_ensemble_coral_reef(self, fixtures: list, effect: EffectParameters, phase: float):
        """Coral reef - colorful sea life with gentle current movement."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['tropical']
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            current = math.sin((nx * 3 + phase) * tau) * 0.05
            sway = math.sin((ny * 4 + phase * 1.5) * tau) * 0.08
            color_pos = (nx * 0.4 + ny * 0.4 + current + sway + phase * 0.2) % 1.0
            depth = 0.5 + 0.3 * (1.0 - ny)
            caustic = abs(math.sin((nx * 8 + ny * 6 + phase * 2) * math.pi)) * 0.2
            brightness = min(1.0, depth + caustic)
            r, g, b = self._interpolate_palette_color(palette, color_pos)
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * brightness)

        for i, fixture in enumerate(cats['movers']):
            pan = math.sin((phase * 0.3 + i * 0.618) * tau) * 20
            tilt = 35 + math.sin((phase * 0.4 + i * 0.5) * tau) * 15
            r, g, b = self._interpolate_palette_color(palette, (phase + i * 0.2) % 1.0)
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.55,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.2) % 1.0)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 45), skip_pan_tilt=True)

    def _apply_ensemble_comet(self, fixtures: list, effect: EffectParameters, phase: float):
        """Comet - bright head streaks across stage with sparkling tail."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        palette = self.GRADIENT_PALETTES['fire']
        tau = 2 * math.pi

        comet_x = (phase * 1.5) % 1.5 - 0.25
        comet_y = 0.3 + 0.15 * math.sin(phase * tau * 0.5)
        tail_length = 0.3

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            dx = nx - comet_x
            dy = ny - comet_y
            dist = (dx*dx + dy*dy) ** 0.5

            if dist < 0.06:
                brightness = 1.0 - dist / 0.06
                r, g, b = 255, 240, 200
            elif dx < 0 and abs(dy) < 0.04 + abs(dx) * 0.15 and abs(dx) < tail_length:
                tail_pos = abs(dx) / tail_length
                brightness = (1.0 - tail_pos) * 0.7
                sparkle = abs(math.sin((nx * 20 + phase * 8) * math.pi)) * 0.3
                brightness += sparkle * (1.0 - tail_pos)
                color_pos = (tail_pos * 0.6) % 1.0
                r, g, b = self._interpolate_palette_color(palette, color_pos)
            else:
                brightness = 0.0
                r, g, b = 0, 0, 0
            
            if brightness > 0.01:
                self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * min(1.0, brightness))
            else:
                self._apply_color_to_pixel(pixel, 0, 0, 0, 0)

        for i, fixture in enumerate(cats['movers']):
            pan = (comet_x - 0.5) * 80
            tilt = 25 + (comet_y - 0.3) * 30
            self._apply_mover_position(fixture, pan, tilt, 255, 230, 180,
                                       intensity_scale * 0.8,
                                       fixture_index=i, phase_offset=phase)

        for fixture in cats['wash'] + cats['other']:
            r, g, b = self._interpolate_palette_color(palette, (phase * 0.3) % 1.0)
            brt = 15 + int(max(0, 1.0 - abs(comet_x - 0.5) * 3) * 40)
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * brt), skip_pan_tilt=True)

    def _apply_ensemble_rgb_parade(self, fixtures: list, effect: EffectParameters, phase: float):
        """RGB parade - red, green, blue zones march across the stage."""
        import math
        cats = self._categorize_fixtures(fixtures)
        intensity_scale = self._get_effective_intensity_scale(effect)
        tau = 2 * math.pi

        all_pixels, bounds = self._get_all_ensemble_pixels(fixtures)
        for pixel in all_pixels:
            nx, ny = self._normalize_pixel_pos(pixel, bounds)
            pos = (nx + phase) % 1.0
            r_zone = max(0, 1.0 - abs(pos - 0.167) * 6) + max(0, 1.0 - abs(pos - 1.167) * 6)
            g_zone = max(0, 1.0 - abs(pos - 0.5) * 6)
            b_zone = max(0, 1.0 - abs(pos - 0.833) * 6)
            pulse = 0.7 + 0.3 * math.sin((ny * 4 + phase * 3) * tau)
            r = int(min(255, r_zone * 255 * pulse))
            g = int(min(255, g_zone * 255 * pulse))
            b = int(min(255, b_zone * 255 * pulse))
            brightness = max(r_zone, g_zone, b_zone) * pulse
            self._apply_color_to_pixel(pixel, r, g, b, intensity_scale * min(1.0, brightness))

        for i, fixture in enumerate(cats['movers']):
            zone = int((phase * 3 + i * 0.5) % 3)
            colors = [(255, 0, 0), (0, 255, 0), (0, 0, 255)]
            r, g, b = colors[zone]
            pan = math.sin((phase + i * 0.618) * tau) * 40
            tilt = 30 + math.sin((phase * 2 + i) * tau) * 15
            self._apply_mover_position(fixture, pan, tilt, r, g, b,
                                       intensity_scale * 0.7,
                                       fixture_index=i, phase_offset=phase)

        for i, fixture in enumerate(cats['wash'] + cats['other']):
            zone = int((phase * 3 + i * 0.3) % 3)
            colors = [(255, 0, 0), (0, 255, 0), (0, 0, 255)]
            r, g, b = colors[zone]
            self.apply_static([fixture], f"#{r:02x}{g:02x}{b:02x}",
                            int(intensity_scale * 50), skip_pan_tilt=True)

    # ==================== STROBE EFFECTS (Intensity-only geometric patterns) ====================
    
    def _get_unified_strobe_canvas(self, fixtures: list) -> tuple:
        """
        Get all strobe channels from all fixtures as a unified canvas.
        Returns (all_strobes, bounds) where bounds = (min_x, max_x, min_y, max_y).
        """
        all_strobes = get_all_strobe_positions(fixtures)
        if not all_strobes:
            return [], (0, 1, 0, 1)
        
        min_x = min(s['canvas_x'] for s in all_strobes)
        max_x = max(s['canvas_x'] for s in all_strobes)
        min_y = min(s['canvas_y'] for s in all_strobes)
        max_y = max(s['canvas_y'] for s in all_strobes)
        
        # Ensure non-zero ranges — expand symmetrically (centre at 0.5)
        if max_x - min_x < 0.001:
            mid_x = (min_x + max_x) * 0.5
            min_x = mid_x - 0.05
            max_x = mid_x + 0.05
        if max_y - min_y < 0.001:
            mid_y = (min_y + max_y) * 0.5
            min_y = mid_y - 0.05
            max_y = mid_y + 0.05
        
        return all_strobes, (min_x, max_x, min_y, max_y)
    
    def _apply_strobe_hscan(self, fixtures: list, effect: EffectParameters, phase: float):
        """Horizontal scan line across strobe channels."""
        all_strobes, bounds = self._get_unified_strobe_canvas(fixtures)
        
        if not all_strobes:
            self._apply_strobe(fixtures, effect, phase)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        max_intensity = int(255 * intensity_scale)
        line_width = 0.2
        
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        scan_pos = -line_width + phase * (1.0 + 2 * line_width)
        
        for strobe in all_strobes:
            nx = self._normalize_pixel_pos(strobe, bounds)[0]
            dist = abs(nx - scan_pos)
            
            if dist < line_width:
                brightness = 1.0 - (dist / line_width)
                intensity = int(max_intensity * brightness)
                self._apply_intensity_to_strobe(strobe, intensity)
            else:
                self._apply_intensity_to_strobe(strobe, 0)
    
    def _apply_strobe_vscan(self, fixtures: list, effect: EffectParameters, phase: float):
        """Vertical scan line across strobe channels."""
        all_strobes, bounds = self._get_unified_strobe_canvas(fixtures)
        
        if not all_strobes:
            self._apply_strobe(fixtures, effect, phase)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        max_intensity = int(255 * intensity_scale)
        line_width = 0.2
        
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        scan_pos = -line_width + phase * (1.0 + 2 * line_width)
        
        for strobe in all_strobes:
            ny = self._normalize_pixel_pos(strobe, bounds)[1]
            dist = abs(ny - scan_pos)
            
            if dist < line_width:
                brightness = 1.0 - (dist / line_width)
                intensity = int(max_intensity * brightness)
                self._apply_intensity_to_strobe(strobe, intensity)
            else:
                self._apply_intensity_to_strobe(strobe, 0)
    
    def _apply_strobe_chase(self, fixtures: list, effect: EffectParameters, phase: float):
        """Sequential chase through strobe channels, ordered by position."""
        all_strobes, bounds = self._get_unified_strobe_canvas(fixtures)
        
        if not all_strobes:
            self._apply_strobe(fixtures, effect, phase)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        max_intensity = int(255 * intensity_scale)
        
        # Sort strobes by Y then X for consistent top-to-bottom, left-to-right chase
        sorted_strobes = sorted(all_strobes, key=lambda s: (s['canvas_y'], s['canvas_x']))
        num_strobes = len(sorted_strobes)
        tail_length = max(1, num_strobes // 4)  # Chase tail length
        
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        # Current position in the chase (0 to num_strobes)
        chase_pos = phase * num_strobes
        
        for idx, strobe in enumerate(sorted_strobes):
            # Distance from chase head
            dist = (chase_pos - idx) % num_strobes
            
            if dist < tail_length:
                # In the tail - fade based on distance from head
                brightness = 1.0 - (dist / tail_length)
                intensity = int(max_intensity * brightness)
                self._apply_intensity_to_strobe(strobe, intensity)
            else:
                self._apply_intensity_to_strobe(strobe, 0)
    
    def _apply_strobe_expand(self, fixtures: list, effect: EffectParameters, phase: float):
        """Expanding ring from center on strobe channels."""
        all_strobes, bounds = self._get_unified_strobe_canvas(fixtures)
        
        if not all_strobes:
            self._apply_strobe(fixtures, effect, phase)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        max_intensity = int(255 * intensity_scale)
        ring_width = 0.2
        
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        # Expand from center (0.5, 0.5) to corner (max radius ~0.7)
        max_radius = 0.8
        ring_radius = phase * max_radius
        
        for strobe in all_strobes:
            nx, ny = self._normalize_pixel_pos(strobe, bounds)
            dist = math.sqrt((nx - 0.5) ** 2 + (ny - 0.5) ** 2)
            ring_dist = abs(dist - ring_radius)
            
            if ring_dist < ring_width:
                brightness = 1.0 - (ring_dist / ring_width)
                intensity = int(max_intensity * brightness)
                self._apply_intensity_to_strobe(strobe, intensity)
            else:
                self._apply_intensity_to_strobe(strobe, 0)
    
    def _apply_strobe_flash(self, fixtures: list, effect: EffectParameters, phase: float):
        """Synchronized flash/pulse on all strobe channels."""
        all_strobes, bounds = self._get_unified_strobe_canvas(fixtures)
        
        if not all_strobes:
            self._apply_strobe(fixtures, effect, phase)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        max_intensity = int(255 * intensity_scale)
        
        # Use sine wave for smooth pulse (0 at start/end, 1 at middle)
        pulse = math.sin(phase * math.pi)
        intensity = int(max_intensity * pulse)
        
        for strobe in all_strobes:
            self._apply_intensity_to_strobe(strobe, intensity)
    
    def _apply_strobe_random(self, fixtures: list, effect: EffectParameters, phase: float):
        """Random sparkle on strobe channels."""
        all_strobes, bounds = self._get_unified_strobe_canvas(fixtures)
        
        if not all_strobes:
            self._apply_strobe(fixtures, effect, phase)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        max_intensity = int(255 * intensity_scale)
        
        # Change pattern every ~50ms (20 times per second)
        pattern_idx = int(phase * 20)
        
        for idx, strobe in enumerate(all_strobes):
            # Pseudo-random based on phase and index
            seed = (pattern_idx * 17 + idx * 31) % 100
            if seed < 30:  # 30% chance to be on
                intensity = max_intensity
            else:
                intensity = 0
            self._apply_intensity_to_strobe(strobe, intensity)
    
    def _apply_strobe_alternating(self, fixtures: list, effect: EffectParameters, phase: float):
        """Alternating even/odd strobe channels, ordered by position."""
        all_strobes, bounds = self._get_unified_strobe_canvas(fixtures)
        
        if not all_strobes:
            self._apply_strobe(fixtures, effect, phase)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        max_intensity = int(255 * intensity_scale)
        
        # Sort strobes by Y then X for consistent alternation pattern
        sorted_strobes = sorted(all_strobes, key=lambda s: (s['canvas_y'], s['canvas_x']))
        
        # Alternate every half cycle
        is_even_phase = phase < 0.5
        
        for idx, strobe in enumerate(sorted_strobes):
            is_even_strobe = idx % 2 == 0
            
            if is_even_strobe == is_even_phase:
                self._apply_intensity_to_strobe(strobe, max_intensity)
            else:
                self._apply_intensity_to_strobe(strobe, 0)
    
    def _apply_strobe_build(self, fixtures: list, effect: EffectParameters, phase: float):
        """Progressive build-up turning on more strobes over time, ordered by position."""
        all_strobes, bounds = self._get_unified_strobe_canvas(fixtures)
        
        if not all_strobes:
            self._apply_strobe(fixtures, effect, phase)
            return
        
        intensity_scale = self._get_effective_intensity_scale(effect)
        max_intensity = int(255 * intensity_scale)
        
        # Sort strobes by Y then X for consistent top-to-bottom, left-to-right build
        sorted_strobes = sorted(all_strobes, key=lambda s: (s['canvas_y'], s['canvas_x']))
        num_strobes = len(sorted_strobes)
        
        if effect.direction == 'backward':
            phase = 1.0 - phase
        
        # How many strobes should be on at this phase
        active_count = int(phase * num_strobes)
        
        for idx, strobe in enumerate(sorted_strobes):
            if idx < active_count:
                self._apply_intensity_to_strobe(strobe, max_intensity)
            else:
                self._apply_intensity_to_strobe(strobe, 0)

    def _apply_movement(self, fixtures: list, effect: EffectParameters, phase: float,
                         start_positions: dict = None, ramp_blend: float = 1.0):
        """Apply movement effect - animate pan/tilt on moving heads.
        
        Args:
            start_positions: If provided, dict of fixture_id -> (pan, tilt) captured
                             before the effect started, for smooth ramp-in blending.
            ramp_blend: 0.0 = use start positions, 1.0 = use full movement target.
        """
        # Check if position preview is active - if so, skip all movement
        if hasattr(self, 'is_position_preview_active') and callable(self.is_position_preview_active):
            if self.is_position_preview_active():
                return  # Don't override position preview
        
        if not fixtures:
            print("[Movement] No fixtures to move!")
            return
        
        pan_range = effect.pan_max - effect.pan_min
        tilt_range = effect.tilt_max - effect.tilt_min
        pan_center = effect.pan_min + pan_range // 2
        tilt_center = effect.tilt_min + tilt_range // 2
        
        # Normalize pattern aliases
        pattern = effect.movement_pattern.lower().replace(' ', '').replace('-', '').replace('_', '')
        
        # Debug output (only on first frame)
        if phase < 0.01:
            print(f"[Movement] Pattern: '{effect.movement_pattern}' -> normalized: '{pattern}'")
            print(f"[Movement] Pan range: {effect.pan_min}-{effect.pan_max}, Tilt range: {effect.tilt_min}-{effect.tilt_max}")
            print(f"[Movement] Fixtures: {[f.label or f.profile.name for f in fixtures]}")
            print(f"[Movement] Intensity range: {effect.intensity_min}-{effect.intensity_max}%")
        
        # Map common terms to canonical patterns
        sweep_patterns = ('sweep', 'scan', 'sidetoside', 'leftright', 'horizontal', 'pansweep', 'wipe', 'pan')
        nod_patterns = ('nod', 'wave', 'updown', 'upanddown', 'vertical', 'tiltwave', 'bob', 'bow', 'headbang', 'tilt')
        circle_patterns = ('circle', 'circular', 'rotate', 'spin', 'orbit', 'around')
        figure8_patterns = ('figure8', 'figureeight', 'infinity', 'eight', 'lemniscate')
        random_patterns = ('random', 'chaos', 'wild', 'crazy', 'ballyhoo', 'party', 'erratic')
        
        # New position-based patterns (use fixture positions for offset timing)
        position_based_patterns = (
            'wave_sweep', 'wavesweep', 'tilt_wave', 'tiltwave', 'spiral', 
            'waterfall', 'converge', 'diverge', 'mirror', 'fan_out', 'fanout',
            'fan_in', 'fanin', 'chase_pan', 'chasepan', 'random_wave', 'randomwave',
            'bounce_wave', 'bouncewave',
            'stagger', 'crossover', 'figure8_wide', 'figure8wide'
        )
        cross_patterns_a = ('cross', 'xpattern', 'plus')
        pendulum_patterns_a = ('pendulum', 'swing', 'metronome')
        zigzag_patterns_a = ('zigzag', 'zag', 'angular', 'sawtooth')
        
        # Get fixture offset setting (0.0 = all sync, 1.0 = max spread)
        fixture_offset = getattr(effect, 'fixture_offset', 0.25)
        
        # Check if we should also do intensity chase (when intensity_min != intensity_max)
        intensity_range = effect.intensity_max - effect.intensity_min
        do_intensity_chase = intensity_range > 10  # Only if there's meaningful range
        
        for i, fixture in enumerate(fixtures):
            # Get fixture's stage position for position-based effects
            fixture_pos_x = getattr(fixture, 'location_x', 0.5)
            fixture_pos_y = getattr(fixture, 'location_y', 0.5)
            
            # Calculate fixture phase offset based on pattern type
            if pattern in position_based_patterns:
                # Use stage position for timing offset
                if pattern in ('waterfall',):
                    # Top-to-bottom: offset by Y position
                    position_offset = fixture_pos_y * fixture_offset
                elif pattern in ('mirror',):
                    # Mirror: use absolute distance from center
                    position_offset = abs(fixture_pos_x - 0.5) * 2 * fixture_offset
                elif pattern in ('converge', 'fan_in', 'fanin'):
                    # Converge: outer fixtures lead, center follows
                    position_offset = (1.0 - abs(fixture_pos_x - 0.5) * 2) * fixture_offset
                elif pattern in ('diverge', 'fan_out', 'fanout'):
                    # Diverge: center leads, outer fixtures follow
                    position_offset = abs(fixture_pos_x - 0.5) * 2 * fixture_offset
                elif pattern in ('random_wave', 'randomwave'):
                    # Random offset per fixture
                    import random
                    random.seed(i * 12345)
                    position_offset = random.random() * fixture_offset
                elif pattern in ('spiral',):
                    # Spiral: combine X and Y for diagonal offset
                    position_offset = (fixture_pos_x + fixture_pos_y) / 2 * fixture_offset
                elif pattern in ('stagger',):
                    # Stagger: sequential by fixture index
                    position_offset = (i / max(len(fixtures), 1)) * fixture_offset
                elif pattern in ('crossover',):
                    # Crossover: left side vs right side opposite
                    position_offset = (0.5 - fixture_pos_x) * fixture_offset
                elif pattern in ('figure8_wide', 'figure8wide'):
                    # Wide figure-8: offset by position
                    position_offset = fixture_pos_x * fixture_offset
                else:
                    # Default: left-to-right offset by X position
                    position_offset = fixture_pos_x * fixture_offset
                
                fixture_phase = (phase + position_offset) % 1.0
            else:
                # Standard fixture-index-based offset
                fixture_phase = (phase + i / max(len(fixtures), 1) * fixture_offset) % 1.0
            
            # Calculate intensity for this fixture (chase pattern if enabled)
            if do_intensity_chase:
                # Chase: one fixture bright at a time, others dim
                # Use a sharper curve for more dramatic on/off effect
                chase_pos = (phase * len(fixtures)) % len(fixtures)
                dist = min(abs(i - chase_pos), len(fixtures) - abs(i - chase_pos))
                # Sharper falloff: fixture is bright only when chase_pos is close
                brightness = max(0, 1 - dist * 0.8)
                intensity = int(effect.intensity_min + intensity_range * brightness)
            else:
                intensity = effect.intensity
            
            _2pi = 2.0 * math.pi
            _fp2pi = fixture_phase * _2pi
            _fp_pi = fixture_phase * math.pi

            if pattern in circle_patterns:
                # Circular motion - full range on both axes
                pan = int(pan_center + (pan_range / 2) * math.cos(_fp2pi))
                tilt = int(tilt_center + (tilt_range / 2) * math.sin(_fp2pi))
            
            elif pattern in figure8_patterns:
                # Figure-8 pattern (lemniscate) - dramatic tilt variation
                pan = int(pan_center + (pan_range / 2) * math.sin(_fp2pi))
                tilt = int(tilt_center + (tilt_range / 2) * math.sin(fixture_phase * 4 * math.pi))
            
            elif pattern in sweep_patterns:
                # Side-to-side pan sweep with moderate tilt variation
                pan = int(effect.pan_min + pan_range * (0.5 + 0.5 * math.sin(_fp2pi)))
                tilt = int(tilt_center + tilt_range * 0.3 * math.sin(_fp_pi))
            
            elif pattern in nod_patterns:
                # Up-down tilt nod with some pan sway
                pan = int(pan_center + pan_range * 0.2 * math.sin(_fp_pi))
                tilt = int(effect.tilt_min + tilt_range * (0.5 + 0.5 * math.sin(_fp2pi)))
            
            elif pattern in random_patterns:
                # Random/ballyhoo - chaotic movement
                import random
                random.seed(int(fixture_phase * 10) + i * 1000)
                pan = random.randint(effect.pan_min, effect.pan_max)
                tilt = random.randint(effect.tilt_min, effect.tilt_max)
            
            elif pattern in cross_patterns_a:
                # Cross / X pattern - sweeps diagonals
                pan = int(pan_center + (pan_range / 2) * math.sin(_fp2pi))
                tilt = int(tilt_center + (tilt_range / 2) * math.cos(_fp2pi))
            
            elif pattern in pendulum_patterns_a:
                # Pendulum - full pan swing with subtle fast tilt
                pan = int(effect.pan_min + pan_range * (0.5 + 0.5 * math.sin(_fp2pi)))
                tilt = int(tilt_center + tilt_range * 0.15 * math.sin(fixture_phase * 6 * math.pi))
            
            elif pattern in zigzag_patterns_a:
                # Zigzag - 4-segment diagonal corners
                seg = int(fixture_phase * 4) % 4
                seg_t = (fixture_phase * 4) % 1.0
                if seg == 0:
                    pan = int(effect.pan_min + pan_range * seg_t)
                    tilt = int(effect.tilt_min + tilt_range * seg_t)
                elif seg == 1:
                    pan = int(effect.pan_max - pan_range * seg_t)
                    tilt = int(effect.tilt_min + tilt_range * seg_t)
                elif seg == 2:
                    pan = int(effect.pan_min + pan_range * seg_t)
                    tilt = int(effect.tilt_max - tilt_range * seg_t)
                else:
                    pan = int(effect.pan_max - pan_range * seg_t)
                    tilt = int(effect.tilt_max - tilt_range * seg_t)
            
            # === POSITION-BASED MOVEMENT PATTERNS ===
            elif pattern in ('wave_sweep', 'wavesweep'):
                # Wave sweep - pan sweep with position-based tilt
                pan = int(effect.pan_min + pan_range * (0.5 + 0.5 * math.sin(_fp2pi)))
                tilt = int(tilt_center + tilt_range * 0.35 * math.sin(_fp_pi))
            
            elif pattern in ('tilt_wave', 'tiltwave'):
                # Tilt wave - nodding with position-based timing
                pan = int(pan_center + pan_range * 0.25 * math.sin(_fp_pi))
                tilt = int(effect.tilt_min + tilt_range * (0.5 + 0.5 * math.sin(_fp2pi)))
            
            elif pattern in ('spiral',):
                # Spiral - expanding/contracting radius with fast spin
                radius = 0.3 + 0.2 * math.sin(_fp2pi)
                pan = int(pan_center + pan_range * radius * math.cos(fixture_phase * 6 * math.pi))
                tilt = int(tilt_center + tilt_range * radius * math.sin(fixture_phase * 6 * math.pi))
            
            elif pattern in ('waterfall',):
                # Waterfall - tilt sweeps down sequentially with gentle pan
                pan = int(pan_center + pan_range * 0.25 * math.sin(_fp_pi * 0.5))
                tilt = int(effect.tilt_min + tilt_range * fixture_phase)
            
            elif pattern in ('converge',):
                # Converge - beams move toward center
                current_pan = int(effect.pan_min + fixture_pos_x * pan_range)
                current_tilt = int(effect.tilt_min + (1.0 - fixture_phase) * tilt_range * 0.5 + tilt_range * 0.25)
                blend = 0.5 + 0.5 * math.sin(_fp2pi)
                pan = int(current_pan + (pan_center - current_pan) * blend)
                tilt = int(current_tilt + (tilt_center - current_tilt) * blend)
            
            elif pattern in ('diverge',):
                # Diverge - beams spread outward from center
                spread_pan = int(effect.pan_min + fixture_pos_x * pan_range)
                spread_tilt = int(effect.tilt_min + tilt_range * 0.3)
                blend = 0.5 + 0.5 * math.sin(_fp2pi)
                pan = int(pan_center + (spread_pan - pan_center) * blend)
                tilt = int(tilt_center + (spread_tilt - tilt_center) * blend)
            
            elif pattern in ('mirror',):
                # Mirror - left fixtures go opposite of right fixtures
                mirror_mult = -1.0 if fixture_pos_x < 0.5 else 1.0
                pan = int(pan_center + (pan_range / 2) * mirror_mult * math.sin(_fp2pi))
                tilt = int(tilt_center + (tilt_range / 2) * math.sin(_fp2pi))
            
            elif pattern in ('fan_out', 'fanout'):
                # Fan out - beams spread from tight to wide
                base_angle = (fixture_pos_x - 0.5) * math.pi
                spread_amount = 0.5 + 0.5 * math.sin(_fp2pi)
                pan = int(pan_center + (pan_range / 2) * math.sin(base_angle) * spread_amount)
                tilt = int(effect.tilt_min + tilt_range * (0.2 + 0.6 * spread_amount))
            
            elif pattern in ('fan_in', 'fanin'):
                # Fan in - beams collapse from wide to tight
                base_angle = (fixture_pos_x - 0.5) * math.pi
                spread_amount = 0.5 - 0.5 * math.sin(_fp2pi)
                pan = int(pan_center + (pan_range / 2) * math.sin(base_angle) * spread_amount)
                tilt = int(effect.tilt_min + tilt_range * (0.2 + 0.6 * (1.0 - spread_amount)))
            
            elif pattern in ('chase_pan', 'chasepan'):
                # Chase pan - sequential pan movement with slight tilt
                pan = int(effect.pan_min + pan_range * (0.5 + 0.5 * math.sin(_fp2pi)))
                tilt = int(tilt_center + tilt_range * 0.1 * math.sin(_fp_pi))
            
            elif pattern in ('random_wave', 'randomwave'):
                # Random wave - each fixture has random timing but same movement
                pan = int(pan_center + (pan_range / 2) * math.sin(_fp2pi))
                tilt = int(tilt_center + (tilt_range / 2) * math.cos(_fp2pi))
            
            elif pattern in ('bounce_wave', 'bouncewave'):
                # Bounce wave - wave bounces back and forth
                bounce_phase = fixture_phase * 2
                if bounce_phase > 1.0:
                    bounce_phase = 2.0 - bounce_phase
                pan = int(effect.pan_min + pan_range * bounce_phase)
                tilt = int(tilt_center + (tilt_range / 2) * math.sin(bounce_phase * math.pi))
            
            elif pattern in ('stagger',):
                # Stagger - full diagonal sweep, sequential per fixture
                pan = int(effect.pan_min + pan_range * (0.5 + 0.5 * math.sin(_fp2pi)))
                tilt = int(effect.tilt_min + tilt_range * (0.5 + 0.5 * math.cos(_fp2pi)))
            
            elif pattern in ('crossover',):
                # Crossover - left side sweeps right, right side sweeps left
                direction = 1.0 if fixture_pos_x < 0.5 else -1.0
                pan = int(pan_center + (pan_range / 2) * direction * math.sin(_fp2pi))
                tilt = int(tilt_center + (tilt_range / 2) * math.sin(_fp_pi))
            
            elif pattern in ('figure8_wide', 'figure8wide'):
                # Wide figure-8 using full range
                pan = int(effect.pan_min + pan_range * (0.5 + 0.5 * math.sin(_fp2pi)))
                tilt = int(effect.tilt_min + tilt_range * (0.5 + 0.5 * math.sin(fixture_phase * 4 * math.pi)))
            
            else:  # 'none' or unknown - default to dramatic sweep with tilt
                if pattern != 'none':
                    pan = int(pan_center + (pan_range / 2) * math.cos(_fp2pi))
                    tilt = int(tilt_center + (tilt_range / 2) * math.sin(_fp_pi))
                else:
                    pan = pan_center
                    tilt = int(tilt_center + (tilt_range / 3) * math.sin(_fp2pi))
            
            # Clamp values
            pan = max(0, min(255, pan))
            tilt = max(0, min(255, tilt))
            
            # --- Smooth ramp-in: blend from captured start position to movement target ---
            if start_positions and ramp_blend < 1.0:
                pan, tilt = self._blend_pan_tilt(fixture.id, pan, tilt, start_positions, ramp_blend)
            
            # Check if rainbow colors are enabled
            rainbow_colors = getattr(effect, 'rainbow_colors', False)
            
            # Check for color palette (for color variety across fixtures)
            color_palette = getattr(effect, 'color_palette', [])
            
            if rainbow_colors:
                # Cycle through colors during movement
                mode = fixture.profile.get_mode(fixture.mode_name) if fixture.profile else None
                has_color_wheel = False
                color_wheel_channel = None
                if mode:
                    for ch in mode.channels:
                        if ch.type.lower() == 'color_wheel':
                            has_color_wheel = True
                            color_wheel_channel = ch
                            break
                
                if has_color_wheel and color_wheel_channel and color_wheel_channel.color_wheel_colors:
                    # Cycle through color wheel colors
                    colors = color_wheel_channel.color_wheel_colors
                    num_colors = len(colors)
                    if num_colors > 1:
                        # Skip white (index 0), cycle through actual colors
                        color_index = 1 + int((phase + fixture_phase) * (num_colors - 1) * 2) % (num_colors - 1)
                    else:
                        color_index = 0
                    color_wheel_value = colors[color_index].get('value', 0)
                    # Check if fixture also has RGB channels
                    has_rgb = any(ch.type.lower() in ('red', 'green', 'blue') for ch in mode.channels)
                    if has_rgb:
                        # Has both color wheel and RGB - send rainbow color to RGB
                        color = get_rainbow_color((phase + fixture_phase) % 1.0)
                        self.apply_static([fixture], color, intensity, pan=pan, tilt=tilt,
                                        color_wheel_value=color_wheel_value,
                                        effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                        **self._gobo_kwargs(effect))
                    else:
                        # Color wheel only
                        self.apply_static([fixture], "#ffffff", intensity, pan=pan, tilt=tilt,
                                        color_wheel_value=color_wheel_value,
                                        effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                        **self._gobo_kwargs(effect))
                else:
                    # RGB rainbow
                    color = get_rainbow_color((phase + fixture_phase) % 1.0)
                    self.apply_static([fixture], color, intensity, pan=pan, tilt=tilt,
                                    color_wheel_value=-1,
                                    effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                    **self._gobo_kwargs(effect))
            elif color_palette and len(color_palette) > 0:
                # Use color palette - each fixture gets a different color from the palette
                fixture_color = color_palette[i % len(color_palette)]
                if phase < 0.02 and i < 5:
                    print(f"[Palette] {fixture.label or fixture.profile.name}: Using palette color {fixture_color}")
                self.apply_static([fixture], fixture_color, intensity, pan=pan, tilt=tilt,
                                color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                **self._gobo_kwargs(effect))
            else:
                # Static color
                self.apply_static([fixture], effect.color, intensity, pan=pan, tilt=tilt,
                                color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                                effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                                **self._gobo_kwargs(effect))
    
    def _fixture_has_pan_tilt(self, fixture) -> bool:
        """Check if a fixture has pan and tilt channels (is a mover)."""
        mode = fixture.profile.get_mode(fixture.mode_name)
        if not mode:
            return False
        has_pan = False
        has_tilt = False
        for ch in mode.channels:
            ch_type = ch.type.lower()
            if ch_type == 'pan':
                has_pan = True
            elif ch_type == 'tilt':
                has_tilt = True
        return has_pan and has_tilt

    
    def _apply_position_cycle_overlay(self, fixtures: list, effect: EffectParameters, current_time: float,
                                      start_positions: dict = None, ramp_blend: float = 1.0) -> bool:
        """Apply position cycling as an overlay on top of any effect.
        
        This cycles through saved position presets, applying pan/tilt only.
        The color/intensity effect continues running independently.
        
        Args:
            start_positions: If provided, dict of fixture_id -> (pan, tilt) captured
                             before the effect started, for smooth ramp-in blending.
            ramp_blend: 0.0 = use start positions, 1.0 = use full movement target.
        """
        # Check if position preview is active - if so, skip ALL position cycling
        if self._is_preview_active():
            return False  # Don't override position preview
        
        # Get position presets from project
        all_presets = self.project.position_presets
        if not all_presets:
            return False
        
        # Filter to selected presets if specified
        if effect.position_cycle_presets:
            presets = [p for p in all_presets if p.id in effect.position_cycle_presets]
        else:
            presets = all_presets
        
        if not presets:
            return False
        
        # Get hold time
        hold_time = getattr(effect, 'position_cycle_hold_time', 4.0)
        
        # Get pan/tilt speed (1-255, higher = faster)
        pan_tilt_speed = getattr(effect, 'position_cycle_speed', 0)
        
        # Calculate time delta
        delta = current_time - self._position_cycle_last_time
        self._position_cycle_last_time = current_time
        self._position_cycle_time += delta
        
        # Check if we need to advance to next position
        if self._position_cycle_time >= hold_time:
            self._position_cycle_time = 0.0
            self._position_cycle_index = (self._position_cycle_index + 1) % len(presets)
            print(f"[Effect] Position cycle -> {presets[self._position_cycle_index].name}")
        
        # Ensure index is valid
        if self._position_cycle_index >= len(presets):
            self._position_cycle_index = 0
        
        # Get current preset
        current_preset = presets[self._position_cycle_index]

        applied_any = False
        
        # Apply pan/tilt to movers
        for fixture in fixtures:
            if not self._fixture_has_pan_tilt(fixture):
                continue
            
            if fixture.id not in current_preset.fixture_positions:
                continue
            
            pos = current_preset.fixture_positions[fixture.id]
            mode = fixture.profile.get_mode(fixture.mode_name)
            if not mode:
                continue
            
            uni = self.artnet.get_universe(fixture.universe)
            if not uni:
                continue
            
            # Compute blended pan/tilt for smooth ramp-in
            target_pan = pos.get('pan', 128)
            target_tilt = pos.get('tilt', 128)
            if start_positions and ramp_blend < 1.0:
                target_pan, target_tilt = self._blend_pan_tilt(
                    fixture.id, target_pan, target_tilt, start_positions, ramp_blend)

            # Batch updates under lock to avoid tearing (pan set without tilt, etc.)
            with (getattr(uni, 'lock', None) or nullcontext()):
                for i, ch in enumerate(mode.channels):
                    ch_type = ch.type.lower()
                    addr = fixture.address + i  # 1-indexed for Art-Net
                    
                    if ch_type == 'pan' and 'pan' in pos:
                        uni.set_channel(addr, target_pan)
                    elif ch_type == 'tilt' and 'tilt' in pos:
                        uni.set_channel(addr, target_tilt)
                    elif ch_type in ('pan_fine', 'tilt_fine'):
                        uni.set_channel(addr, 0)
                    elif ch_type in ('pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'pan_speed', 'tilt_speed', 'speed'):
                        # Some profiles use generic 'speed' for pan/tilt speed.
                        uni.set_channel(addr, pan_tilt_speed)

            applied_any = True

        return applied_any
    
    def _apply_movement_pan_tilt_only(self, fixtures: list, effect: EffectParameters, phase: float,
                                      start_positions: dict = None, ramp_blend: float = 1.0):
        """Apply ONLY pan/tilt movement to moving heads, without changing color/intensity.
        
        This is called after the main effect (pulse, chase, etc.) has set color/intensity,
        so we only need to update the pan/tilt channels.
        
        Args:
            start_positions: If provided, dict of fixture_id -> (pan, tilt) captured
                             before the effect started, for smooth ramp-in blending.
            ramp_blend: 0.0 = use start positions, 1.0 = use full movement target.
        """
        # Check if position preview is active - if so, skip all movement
        if hasattr(self, 'is_position_preview_active') and callable(self.is_position_preview_active):
            if self.is_position_preview_active():
                return  # Don't override position preview
        
        if not fixtures:
            print("[_apply_movement_pan_tilt_only] No fixtures to move!")
            return

        # Use float math for smooth movement; map to 16-bit DMX when writing
        pan_range = float(effect.pan_max - effect.pan_min)
        tilt_range = float(effect.tilt_max - effect.tilt_min)
        pan_center = float(effect.pan_min) + pan_range / 2.0
        tilt_center = float(effect.tilt_min) + tilt_range / 2.0

        # Normalize pattern aliases (match _apply_movement)
        pattern = (effect.movement_pattern or '').lower().replace(' ', '').replace('-', '').replace('_', '')

        sweep_patterns = ('sweep', 'scan', 'sidetoside', 'leftright', 'horizontal', 'pansweep', 'wipe', 'pan')
        nod_patterns = ('nod', 'wave', 'updown', 'upanddown', 'vertical', 'tiltwave', 'bob', 'bow', 'headbang', 'tilt')
        circle_patterns = ('circle', 'circular', 'rotate', 'spin', 'orbit', 'around')
        figure8_patterns = ('figure8', 'figureeight', 'infinity', 'eight', 'lemniscate')
        random_patterns = ('random', 'chaos', 'wild', 'crazy', 'ballyhoo', 'party', 'erratic')

        # Full pattern set supported by the GUI movement buttons
        position_based_patterns = (
            'wave_sweep', 'wavesweep', 'tilt_wave', 'tiltwave', 'spiral',
            'waterfall', 'converge', 'diverge', 'mirror', 'fan_out', 'fanout',
            'fan_in', 'fanin', 'chase_pan', 'chasepan', 'random_wave', 'randomwave',
            'bounce_wave', 'bouncewave',
            'stagger', 'crossover', 'figure8_wide', 'figure8wide',
        )
        # New synced patterns
        cross_patterns = ('cross', 'xpattern', 'plus')
        pendulum_patterns = ('pendulum', 'swing', 'metronome')
        zigzag_patterns = ('zigzag', 'zag', 'angular', 'sawtooth')

        fixture_offset = getattr(effect, 'fixture_offset', 0.25)

        for fixture_idx, fixture in enumerate(fixtures):
            fixture_pos_x = getattr(fixture, 'location_x', 0.5)
            fixture_pos_y = getattr(fixture, 'location_y', 0.5)

            if pattern in position_based_patterns:
                if pattern in ('waterfall',):
                    position_offset = fixture_pos_y * fixture_offset
                elif pattern in ('mirror',):
                    position_offset = abs(fixture_pos_x - 0.5) * 2 * fixture_offset
                elif pattern in ('converge', 'fan_in', 'fanin'):
                    position_offset = (1.0 - abs(fixture_pos_x - 0.5) * 2) * fixture_offset
                elif pattern in ('diverge', 'fan_out', 'fanout'):
                    position_offset = abs(fixture_pos_x - 0.5) * 2 * fixture_offset
                elif pattern in ('random_wave', 'randomwave'):
                    import random
                    random.seed(fixture_idx * 12345)
                    position_offset = random.random() * fixture_offset
                elif pattern in ('spiral',):
                    position_offset = (fixture_pos_x + fixture_pos_y) / 2 * fixture_offset
                elif pattern in ('crossover',):
                    # Left side gets positive offset, right gets negative → crossing
                    position_offset = (fixture_pos_x - 0.5) * fixture_offset
                elif pattern in ('stagger',):
                    # Sequential stagger based on fixture index within the set
                    position_offset = fixture_idx / max(len(fixtures), 1) * fixture_offset
                elif pattern in ('figure8_wide', 'figure8wide'):
                    position_offset = fixture_pos_x * fixture_offset
                else:
                    position_offset = fixture_pos_x * fixture_offset

                fixture_phase = (phase + position_offset) % 1.0
            else:
                fixture_phase = (phase + fixture_idx / max(len(fixtures), 1) * fixture_offset) % 1.0

            # Compute continuous pan/tilt positions (float, 0-255 range)
            # All patterns now use the FULL user-defined range for dramatic movement.
            _2pi = 2.0 * math.pi
            _fp2pi = fixture_phase * _2pi
            _fp_pi = fixture_phase * math.pi

            if pattern in circle_patterns:
                pan_pos = pan_center + (pan_range / 2.0) * math.cos(_fp2pi)
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.sin(_fp2pi)
            elif pattern in figure8_patterns:
                pan_pos = pan_center + (pan_range / 2.0) * math.sin(_fp2pi)
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.sin(fixture_phase * 4.0 * math.pi)
            elif pattern in sweep_patterns:
                # Full-range horizontal pan sweep with gentle tilt sway
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = tilt_center + (tilt_range * 0.3) * math.sin(_fp_pi)
            elif pattern in nod_patterns:
                # Primarily tilt with subtle pan variation — uses full tilt range
                pan_pos = pan_center + (pan_range * 0.2) * math.sin(_fp_pi)
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.5 + 0.5 * math.sin(_fp2pi))
            elif pattern in cross_patterns:
                # X / cross pattern — pan and tilt sweep independently at 90° offset
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.5 + 0.5 * math.cos(_fp2pi))
            elif pattern in pendulum_patterns:
                # Large swinging pan like a pendulum — very dramatic
                # Use a smoothed triangle wave for more natural swing feel
                _t = fixture_phase % 1.0
                swing = math.sin(_fp_pi) ** 2  # ease-in-out half-period
                if _t > 0.5:
                    swing = -swing
                pan_pos = pan_center + (pan_range / 2.0) * math.sin(_fp2pi)
                tilt_pos = tilt_center + (tilt_range * 0.15) * math.sin(fixture_phase * 4.0 * math.pi)
            elif pattern in zigzag_patterns:
                # Sharp diagonal zigzag — alternating between corners
                _seg = (fixture_phase * 4.0) % 4.0
                if _seg < 1.0:
                    # Top-left to bottom-right
                    pan_pos = float(effect.pan_min) + pan_range * _seg
                    tilt_pos = float(effect.tilt_min) + tilt_range * _seg
                elif _seg < 2.0:
                    # Bottom-right to top-right
                    _t = _seg - 1.0
                    pan_pos = float(effect.pan_max) - pan_range * 0.0
                    tilt_pos = float(effect.tilt_max) - tilt_range * _t
                elif _seg < 3.0:
                    # Top-right to bottom-left
                    _t = _seg - 2.0
                    pan_pos = float(effect.pan_max) - pan_range * _t
                    tilt_pos = float(effect.tilt_min) + tilt_range * _t
                else:
                    # Bottom-left to top-left
                    _t = _seg - 3.0
                    pan_pos = float(effect.pan_min)
                    tilt_pos = float(effect.tilt_max) - tilt_range * _t
            elif pattern in random_patterns:
                import random
                random.seed(int(fixture_phase * 10) + fixture_idx * 1000)
                pan_pos = float(random.randint(effect.pan_min, effect.pan_max))
                tilt_pos = float(random.randint(effect.tilt_min, effect.tilt_max))
            elif pattern in ('wave_sweep', 'wavesweep'):
                # Full-range pan wave with moderate tilt wave
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = tilt_center + (tilt_range * 0.35) * math.sin(_fp_pi)
            elif pattern in ('tilt_wave', 'tiltwave'):
                # Full tilt sweep with moderate pan variation
                pan_pos = pan_center + (pan_range * 0.25) * math.sin(_fp_pi)
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.5 + 0.5 * math.sin(_fp2pi))
            elif pattern in ('spiral',):
                # Expanding/contracting spiral — radius oscillates
                radius_frac = 0.3 + 0.7 * (0.5 + 0.5 * math.sin(fixture_phase * math.pi))
                pan_pos = pan_center + (pan_range / 2.0) * radius_frac * math.cos(_fp2pi * 3.0)
                tilt_pos = tilt_center + (tilt_range / 2.0) * radius_frac * math.sin(_fp2pi * 3.0)
            elif pattern in ('waterfall',):
                # Full tilt sweep top-to-bottom with gentle pan sway
                pan_pos = pan_center + (pan_range * 0.25) * math.sin(_fp_pi * 0.5)
                tilt_pos = float(effect.tilt_min) + tilt_range * float(fixture_phase)
            elif pattern in ('converge',):
                # Beams converge toward center of the pan/tilt range
                target_pan = pan_center
                target_tilt = tilt_center
                start_pan = float(effect.pan_min) + fixture_pos_x * pan_range
                start_tilt = float(effect.tilt_min) + tilt_range * 0.2
                blend = 0.5 + 0.5 * math.sin(_fp2pi)
                pan_pos = start_pan + (target_pan - start_pan) * blend
                tilt_pos = start_tilt + (target_tilt - start_tilt) * blend
            elif pattern in ('diverge',):
                # Beams spread outward from center
                spread_pan = float(effect.pan_min) + fixture_pos_x * pan_range
                spread_tilt = float(effect.tilt_min) + tilt_range * 0.2
                blend = 0.5 + 0.5 * math.sin(_fp2pi)
                pan_pos = pan_center + (spread_pan - pan_center) * blend
                tilt_pos = tilt_center + (spread_tilt - tilt_center) * blend
            elif pattern in ('mirror',):
                is_left = fixture_pos_x < 0.5
                mirror_mult = -1.0 if is_left else 1.0
                pan_pos = pan_center + (pan_range / 2.0) * mirror_mult * math.sin(_fp2pi)
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.sin(_fp2pi)
            elif pattern in ('fan_out', 'fanout'):
                base_angle = (fixture_pos_x - 0.5) * math.pi
                spread_amount = 0.5 + 0.5 * math.sin(_fp2pi)
                pan_pos = pan_center + (pan_range / 2.0) * math.sin(base_angle) * spread_amount
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.2 + 0.6 * spread_amount)
            elif pattern in ('fan_in', 'fanin'):
                base_angle = (fixture_pos_x - 0.5) * math.pi
                spread_amount = 0.5 - 0.5 * math.sin(_fp2pi)
                pan_pos = pan_center + (pan_range / 2.0) * math.sin(base_angle) * spread_amount
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.2 + 0.6 * (1.0 - spread_amount))
            elif pattern in ('chase_pan', 'chasepan'):
                # Full pan sweep with tilt staying near center
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = tilt_center + (tilt_range * 0.1) * math.sin(_fp_pi)
            elif pattern in ('random_wave', 'randomwave'):
                # Circular path (different from plain circle due to position-based offset)
                pan_pos = pan_center + (pan_range / 2.0) * math.sin(_fp2pi)
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.cos(_fp2pi)
            elif pattern in ('bounce_wave', 'bouncewave'):
                bounce_phase = fixture_phase * 2.0
                if bounce_phase > 1.0:
                    bounce_phase = 2.0 - bounce_phase
                pan_pos = float(effect.pan_min) + pan_range * bounce_phase
                tilt_pos = tilt_center + (tilt_range / 2.0) * math.sin(bounce_phase * math.pi)
            elif pattern in ('stagger',):
                # Each fixture does a full diagonal sweep, offset in time
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.5 + 0.5 * math.cos(_fp2pi))
            elif pattern in ('crossover',):
                # Left fixtures sweep right, right fixtures sweep left — beams cross
                direction_mult = 1.0 if fixture_pos_x < 0.5 else -1.0
                pan_pos = pan_center + (pan_range / 2.0) * direction_mult * math.sin(_fp2pi)
                tilt_pos = tilt_center + (tilt_range * 0.4) * math.sin(_fp2pi)
            elif pattern in ('figure8_wide', 'figure8wide'):
                # Wide figure-8 using the full pan AND tilt range for dramatic motion
                pan_pos = float(effect.pan_min) + pan_range * (0.5 + 0.5 * math.sin(_fp2pi))
                tilt_pos = float(effect.tilt_min) + tilt_range * (0.5 + 0.5 * math.sin(fixture_phase * 4.0 * math.pi))
            else:
                # Unknown pattern: default to a dramatic sweep
                pan_pos = pan_center + (pan_range / 2.0) * math.cos(_fp2pi)
                tilt_pos = tilt_center + (tilt_range * 0.4) * math.sin(_fp_pi)
            
            # Map to 16-bit domain for smooth fine control
            pan16_min = int(effect.pan_min) << 8
            pan16_max = int(effect.pan_max) << 8
            tilt16_min = int(effect.tilt_min) << 8
            tilt16_max = int(effect.tilt_max) << 8
            pan16 = int(max(pan16_min, min(pan16_max, int(pan_pos * 256.0))))
            tilt16 = int(max(tilt16_min, min(tilt16_max, int(tilt_pos * 256.0))))
            
            # --- Smooth ramp-in: blend from captured start position to movement target ---
            if start_positions and ramp_blend < 1.0:
                pan16, tilt16 = self._blend_pan_tilt_16bit(
                    fixture.id, pan16, tilt16, start_positions, ramp_blend)
            
            pan_coarse = (pan16 >> 8) & 0xFF
            pan_fine = pan16 & 0xFF
            tilt_coarse = (tilt16 >> 8) & 0xFF
            tilt_fine = tilt16 & 0xFF
            
            # Only set pan/tilt channels (coarse + fine), leave everything else as-is
            mode = fixture.profile.get_mode(fixture.mode_name)
            if mode:
                uni = self.artnet.get_universe(fixture.universe)
                if not uni:
                    continue

                # Batch updates under lock so output thread can't sample half-written pan/tilt.
                with (getattr(uni, 'lock', None) or nullcontext()):
                    for ch_idx, ch in enumerate(mode.channels):
                        ch_type = ch.type.lower()
                        dmx_addr = fixture.address + ch_idx
                        if ch_type == 'pan':
                            uni.set_channel(dmx_addr, pan_coarse)
                        elif ch_type == 'pan_fine':
                            uni.set_channel(dmx_addr, pan_fine)
                        elif ch_type == 'tilt':
                            uni.set_channel(dmx_addr, tilt_coarse)
                        elif ch_type == 'tilt_fine':
                            uni.set_channel(dmx_addr, tilt_fine)
                        elif ch_type in ('pan_tilt_speed', 'pantilt_speed', 'pt_speed', 'pan_speed', 'tilt_speed', 'speed'):
                            uni.set_channel(dmx_addr, 0)  # Fastest — let software interpolation control smoothness

    def _apply_macro(self, fixtures: list, effect: EffectParameters):
        """Apply macro effect - set fixture type/macro channel to trigger built-in effects."""
        for fixture in fixtures:
            self.apply_static([fixture], effect.color, effect.intensity, macro=effect.macro_value,
                            color_wheel_value=getattr(effect, 'color_wheel_value', -1),
                            effect_channel_value=getattr(effect, 'effect_channel_value', -1),
                            skip_pan_tilt=True,
                            **self._gobo_kwargs(effect))
    def _apply_blackout(self, fixtures: list):
        """Apply blackout - all lights off, but keep pan/tilt where they are."""
        self.apply_static(fixtures, "#000000", 0, skip_pan_tilt=True)
