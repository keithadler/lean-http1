import socket, sys, threading, time
port = int(sys.argv[1]); logf = sys.argv[2]
srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
srv.bind(("127.0.0.1", port)); srv.listen(16)
def handle(c):
    c.settimeout(1.0); data = b""
    try:
        while True:
            b = c.recv(4096)
            if not b: break
            data += b
            # respond so proxy completes; keep reading for pipelined
            try: c.sendall(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nConnection: keep-alive\r\n\r\nok")
            except OSError: pass
    except socket.timeout: pass
    except OSError: pass
    with open(logf, "ab") as f:
        f.write(b"=== CONN ===\n" + data + b"\n")
    c.close()
while True:
    try:
        c,_ = srv.accept(); threading.Thread(target=handle, args=(c,), daemon=True).start()
    except KeyboardInterrupt: break
