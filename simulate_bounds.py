#!/usr/bin/env python3
"""Simulate session bounds calculation with test data"""
import json

# Load the test timeline
with open('C:\\Users\\mattj\\Desktop\\test_session.timeline') as f:
    timeline_data = json.load(f)

print(f"Loaded {len(timeline_data)} events")
print(f"Events: {timeline_data}\n")

# Simulate _update_canvas_view calculation
zoom_level = 50  # Default zoom
canvas_height = 600  # Typical canvas height
padding = 10

# Simulate the calculation as done in the code
session_bounds = {}
session_order = []
session_universes = {}

# First pass: gather sessions and universes
for evt in timeline_data:
    s_id = evt.get("session", 1)
    universe = evt.get("universe", 0)
    if s_id not in session_universes:
        session_universes[s_id] = []
        session_order.append(s_id)
    if universe not in session_universes[s_id]:
        session_universes[s_id].append(universe)

print(f"Sessions found: {session_order}")
print(f"Session universes: {session_universes}\n")

# Initialize bounds
for s_id in session_order:
    session_bounds[s_id] = [float('inf'), float('-inf'), float('inf'), float('-inf')]

# Iterate through events and accumulate bounds
base_y = 130  # waveform_y_bottom (30) + gap (30) = 60, but let's use test value
row_spacing = 24
session_rows = {s_id: base_y for s_id in session_order}

# Compute universe row indices
session_universe_index = {
    s_id: {u: idx for idx, u in enumerate(session_universes[s_id])}
    for s_id in session_order
}

print("Processing frames:")
for frame_idx, evt in enumerate(timeline_data):
    universe = evt.get("universe", 0)
    opcode = evt.get("opcode", 80)
    time_val = evt.get("t", 0)
    session_id = evt.get("session", 1)
    x = time_val * zoom_level
    
    # Row within this session
    universe_idx_map = session_universe_index.get(session_id, {})
    row_idx = universe_idx_map.get(universe, 0)
    y = session_rows[session_id] + row_idx * row_spacing
    
    # Frame dimensions
    block_width = max(8, zoom_level // 10)  # = 5
    block_height = 14
    
    print(f"  Frame {frame_idx}: session={session_id}, universe={universe}, t={time_val}, x={x}, y={y}")
    print(f"    Block: x={x-block_width}-{x+block_width}, y={y-block_height}-{y+block_height}")
    
    # Update bounds
    b = session_bounds[session_id]
    b[0] = min(b[0], x - block_width)
    b[1] = max(b[1], x + block_width)
    b[2] = min(b[2], y - block_height)
    b[3] = max(b[3], y + block_height)

print(f"\nRaw session bounds (before padding): {session_bounds}")

# Apply padding
padded_bounds = {}
for s_id, b in session_bounds.items():
    if b[0] != float('inf'):
        padded = (
            b[0] - padding,
            b[1] + padding,
            b[2] - padding,
            b[3] + padding
        )
        padded_bounds[s_id] = padded
        print(f"Session {s_id}: {padded}")

print(f"\ntest_session.timeline.meta would need:")
print("- session_names: {'1': 'Session 1'} or similar")
print("- markers: []")
print("- loop_enabled: False")
print("- loop_start: 0")
print("- loop_end: 0")

# Test click detection
print(f"\nTest click at (150, 155):")
for s_id, (x1, x2, y1, y2) in padded_bounds.items():
    canvas_x, canvas_y = 150, 155
    hit = x1 <= canvas_x <= x2 and y1 <= canvas_y <= y2
    print(f"  Session {s_id} bounds: x[{x1}, {x2}], y[{y1}, {y2}] -> Hit: {hit}")
