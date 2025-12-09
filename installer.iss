[Setup]
AppName=Timeline Editor
AppVersion=1.0.0
DefaultDirName={pf}\TimelineEditor
DefaultGroupName=Timeline Editor
OutputDir=dist
OutputBaseFilename=TimelineEditor-Setup
Compression=lzma
SolidCompression=yes

[Files]
Source: "dist\TimelineEditor\*"; DestDir: "{app}"; Flags: recursesubdirs

[Icons]
Name: "{group}\Timeline Editor"; Filename: "{app}\TimelineEditor.exe"
Name: "{commondesktop}\Timeline Editor"; Filename: "{app}\TimelineEditor.exe"; Tasks: desktopicon

[Tasks]
Name: "desktopicon"; Description: "Create a desktop icon"; GroupDescription: "Additional icons:"