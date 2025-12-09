#!/usr/bin/env python3
"""Debug script to check session bounds"""

with open('C:\\Users\\mattj\\Desktop\\timeline\\gui.py', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Check the initialization in _on_canvas_click
print("Checking click handler:")
for i, line in enumerate(lines):
    if 'def _on_canvas_click' in line:
        # Print 35 lines of the method
        for j in range(i, min(i+35, len(lines))):
            print(f'{j+1:4d}: {lines[j].rstrip()}')
        break

print("\n\nChecking session_bounds tuple unpacking:")
for i, line in enumerate(lines):
    if 'for s_id, (x1, x2, y1, y2) in self.session_bounds.items()' in line:
        # Show context
        for j in range(max(0, i-2), min(i+5, len(lines))):
            print(f'{j+1:4d}: {lines[j].rstrip()}')
        print()
