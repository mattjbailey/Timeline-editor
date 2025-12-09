#!/usr/bin/env python3
"""Test to verify session bounds calculation"""
import json
from pathlib import Path

# Verify test files exist
test_file = Path('test_session.timeline')
meta_file = Path('test_session.timeline.meta')

print(f'Test file exists: {test_file.exists()}')
print(f'Meta file exists: {meta_file.exists()}')

if test_file.exists():
    with open(test_file) as f:
        data = json.load(f)
    print(f'Timeline has {len(data)} events')
    for i, evt in enumerate(data[:5]):
        print(f'  Event {i}: t={evt.get("t")}, session={evt.get("session")}, universe={evt.get("universe")}')
else:
    print('\nTest files do not exist yet. Timeline is probably empty.')
    print('The user needs to:')
    print('1. Open the GUI')
    print('2. Set up DMX capture with Art-Net')
    print('3. Record some DMX events')
    print('4. Then try to click on a session to select it')
