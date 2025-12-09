#!/usr/bin/env bash
set -euo pipefail

python3 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip
pip install -r requirements.txt
pip install pyinstaller mido python-rtmidi

# Use spec to produce .app
pyinstaller TimelineEditor_mac.spec

echo "Built app at dist/TimelineEditor/TimelineEditor.app"