## Build and Installer

- Prerequisites:
	- Python 3.10+ installed
	- PowerShell on Windows
	- Inno Setup (optional, for installer)

- Set up environment:
```
python -m venv .venv
.\.venv\Scripts\Activate.ps1
pip install -r requirements.txt
pip install pyinstaller
```

- Run locally:
```
python main.py
```

- Build EXE (onedir recommended):
```
pyinstaller --noconsole --onedir --name TimelineEditor \
	--icon "assets\icon.ico" \
	--add-data "timeline;timeline" \
	--add-data "dmx_filter_config.json;." \
	--hidden-import pythonosc.osc_message_builder \
	--hidden-import pythonosc.osc_message \
	main.py
```

- Output:
	- `dist/TimelineEditor/TimelineEditor.exe`

- Create installer with Inno Setup:
	- Open `installer.iss` in Inno Setup and Build.
	- Output: `dist/TimelineEditor-Setup.exe`
	- Optional: set `SetupIconFile=assets\icon.ico` and update `AppVersion`.

- VS Code Task:
	- Use the task "Build TimelineEditor (PyInstaller onedir)" from the Command Palette to build.
	- If `assets\icon.ico` exists, the EXE will show your icon.

### macOS Build (develop on a Mac)

- Prerequisites:
	- Xcode Command Line Tools (`xcode-select --install`)
	- Python 3.10+ (`brew install python` recommended)

- Create environment and install deps:
```
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
pip install pyinstaller mido python-rtmidi
```

- Build app bundle (onedir):
```
pyinstaller --windowed --onedir --name TimelineEditor \
	--icon assets/icon.icns \
	--add-data "timeline:timeline" \
	--add-data "dmx_filter_config.json:." \
	--hidden-import pythonosc.osc_message_builder \
	--hidden-import pythonosc.osc_message \
	main.py
```
Or use the spec for a .app bundle:
```
pyinstaller TimelineEditor_mac.spec
```

- Output:
	- `dist/TimelineEditor/TimelineEditor.app`

- Notes:
	- MIDI on macOS uses `mido` + `python-rtmidi` (CoreMIDI). Windows-only MIDI paths are ignored.
	- Verbose logs on macOS: `~/Library/Logs/Timeline/debug.txt`.
	- For distribution, code signing and notarization are recommended.

### macOS CI Build (GitHub Actions)

- A workflow at `.github/workflows/macos-build.yml` builds the app on macOS and uploads `TimelineEditor-macOS.zip`.
- Trigger it on GitHub under Actions → macOS App Build → Run workflow.

### Local mac build script

- On a Mac, you can also run:
```
bash scripts/build_mac.sh
```
It sets up a venv, installs deps, and builds `dist/TimelineEditor/TimelineEditor.app`.

