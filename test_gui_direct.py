#!/usr/bin/env python3
"""Open timeline directly in the GUI for testing"""
import sys
sys.path.insert(0, 'C:\\Users\\mattj\\Desktop\\timeline')

from gui import TimelineGUI
import tkinter as tk

root = tk.Tk()
app = TimelineGUI(root)

# Load the test timeline
app.load_timeline('C:\\Users\\mattj\\Desktop\\test_session.timeline')

root.mainloop()
