"""DMX Art-Net Timeline Recorder."""
import socket
import time
import threading
import base64


class Recorder:
    """Record DMX events from Art-Net."""
    
    def __init__(self, port=6454):
        self.port = port
        self.recording = False
        self.events = []
        self.sock = None
    
    def start(self):
        """Start recording."""
        self.recording = True
        self.events = []
        
        def record_thread():
            try:
                self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                self.sock.bind(("", self.port))
                self.sock.settimeout(0.1)
                
                start_time = time.perf_counter()
                
                while self.recording:
                    try:
                        data, addr = self.sock.recvfrom(4096)
                        elapsed = time.perf_counter() - start_time
                        
                        if len(data) > 18:
                            universe = data[14] if len(data) > 14 else 0
                            dmx_data = data[18:18+512] if len(data) > 18 else b""
                            payload_b64 = base64.b64encode(dmx_data).decode()
                            
                            evt = {
                                "t": elapsed,
                                "universe": universe,
                                "opcode": 80,
                                "session": 1,
                                "payload": payload_b64
                            }
                            self.events.append(evt)
                    except socket.timeout:
                        continue
                
                self.sock.close()
            except Exception as e:
                print(f"Record error: {e}")
        
        thread = threading.Thread(target=record_thread, daemon=True)
        thread.start()
    
    def stop(self):
        """Stop recording."""
        self.recording = False
        if self.sock:
            try:
                self.sock.close()
            except:
                pass
    
    def get_events(self):
        """Get recorded events."""
        return self.events
