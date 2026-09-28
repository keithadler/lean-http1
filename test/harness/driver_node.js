// Node/llhttp framing driver. For each corpus vector, send the raw bytes to a local http.Server over a
// TCP socket and observe how Node frames the request: rejected (clientError / 400), or accepted with a
// content-length or chunked body. Output: one JSON line {name, verdict} per vector.
//
// Node's HTTP parser is llhttp, the same engine used well beyond Node. Node rejects several ambiguous
// framings by default (a CL+TE request, invalid Content-Length); those show up as "reject".

const http = require("http");
const net = require("net");
const fs = require("fs");
const path = require("path");

const vecPath = path.join(__dirname, "..", "corpus", "vectors.json");
const vectors = JSON.parse(fs.readFileSync(vecPath, "utf8")).vectors;

const results = {};
let current = null;

const server = http.createServer((req, res) => {
  let n = 0;
  req.on("data", (c) => (n += c.length));
  req.on("end", () => {
    const te = (req.headers["transfer-encoding"] || "").toLowerCase();
    let verdict;
    if (te.includes("chunked")) verdict = "chunked";
    else if (req.headers["content-length"] !== undefined)
      verdict = "length:" + parseInt(req.headers["content-length"], 10);
    else verdict = "length:" + n;
    if (current && results[current] === undefined) results[current] = verdict;
    res.end();
  });
});

server.on("clientError", () => {
  if (current && results[current] === undefined) results[current] = "reject";
});

function sendOne(name, hexs) {
  return new Promise((resolve) => {
    current = name;
    const raw = Buffer.from(hexs, "hex");
    const addr = server.address();
    const sock = net.connect(addr.port, "127.0.0.1", () => sock.end(raw));
    let done = false;
    const finish = () => {
      if (done) return;
      done = true;
      if (results[name] === undefined) results[name] = "incomplete";
      sock.destroy();
      resolve();
    };
    sock.on("close", finish);
    sock.on("error", finish);
    setTimeout(finish, 300);
  });
}

server.listen(0, "127.0.0.1", async () => {
  for (const [name, hexs] of Object.entries(vectors)) {
    await sendOne(name, hexs);
  }
  for (const [name] of Object.entries(vectors)) {
    console.log(JSON.stringify({ name, verdict: results[name] || "incomplete" }));
  }
  server.close();
});
