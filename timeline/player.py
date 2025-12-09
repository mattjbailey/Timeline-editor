"""DMX Art-Net Timeline Player."""
import socket
import time
import base64
import threading


class Player:
    """Play back DMX events via Art-Net."""
    
    def __init__(self, target="255.255.255.255", port=6454):
        self.target = target
        self.port = port
        self.playing = False
    
    def play(self, events, speed=1.0):
        """Play back events."""
        self.playing = True
        
        def playback_thread():
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
                
                start_time = time.perf_counter()
                
                while self.playing:
                    elapsed = (time.perf_counter() - start_time) * speed
                    
                    for evt in events:
                        evt_time = evt.get("t", 0)
                        if abs(evt_time - elapsed) < 0.05:
                            payload_b64 = evt.get("payload", "")
                            try:
                                payload = base64.b64decode(payload_b64) if payload_b64 else b""
                                if payload:
                                    sock.sendto(payload, (self.target, self.port))
                            except:
                                pass
                    
                    if elapsed > max((e.get("t", 0) for e in events), default=0):
                        break
                    
                    time.sleep(0.016)
                
                sock.close()
            except Exception as e:
                print(f"Playback error: {e}")
        
        thread = threading.Thread(target=playback_thread, daemon=True)
        thread.start()
    
    def stop(self):
        """Stop playback."""
        self.playing = False
