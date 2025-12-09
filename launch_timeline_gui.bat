@echo off
cd /d "%~dp0"
.\.venv\Scripts\python.exe -m timeline.gui > debug.txt
pause
