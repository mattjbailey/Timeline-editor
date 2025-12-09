from timeline.gui import TimelineEditorGUI
import tkinter as tk

def main():
    root = tk.Tk()
    app = TimelineEditorGUI(root)
    root.mainloop()

if __name__ == "__main__":
    main()