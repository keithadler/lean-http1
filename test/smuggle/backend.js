// Boundary backend. A real HTTP server (Node/llhttp) that records, per request it parses, the method and
// path and body length, appended to a log file. Each test tags its requests with the vector name in the
// path, so the harness can read back exactly which requests reached the backend and how they were framed.
//
//   node backend.js <port> <logfile>
//
// This is the back end of a proxy->backend pair. What it logs is what the proxy in front of it framed and
// forwarded: if a proxy and this backend disagree about where a request ends, the log shows it (an extra
// request, or a request the proxy meant to be body).

const http = require("http");
const fs = require("fs");

const port = parseInt(process.argv[2], 10);
const logfile = process.argv[3];

const server = http.createServer((req, res) => {
  let n = 0;
  req.on("data", (c) => (n += c.length));
  req.on("end", () => {
    fs.appendFileSync(logfile, JSON.stringify({ method: req.method, path: req.url, bodyLen: n }) + "\n");
    res.writeHead(200, { "Content-Length": "2" });
    res.end("ok");
  });
});

server.on("clientError", (err, sock) => {
  try {
    fs.appendFileSync(logfile, JSON.stringify({ clientError: String(err.code || err.message) }) + "\n");
    sock.destroy();
  } catch (_) {}
});

server.listen(port, "127.0.0.1", () => console.log("backend on " + port));
