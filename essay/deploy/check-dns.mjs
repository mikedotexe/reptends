// Read-only launch check. Uses this machine's ordinary DNS with no overrides.
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { lookup, resolve4, resolve6 } from "node:dns/promises";
import { readFile } from "node:fs/promises";
import { request as httpRequest } from "node:http";
import { request as httpsRequest } from "node:https";

const hostname = "reptends.mikedotexe.com";
const siteURL = "https://" + hostname;
const digest = value => createHash("sha256").update(value).digest("hex");
const expectedHash = digest(await readFile(new URL("../dist/index.html", import.meta.url)));
const expectedRobots = await readFile(new URL("../dist/robots.txt", import.meta.url));
const expectedRobotsHash = digest(expectedRobots);

function get(address) {
  const url = new URL(address);
  return new Promise((resolveResponse, reject) => {
    const request = url.protocol === "https:" ? httpsRequest : httpRequest;
    const pending = request(url, {
      agent: false,
      signal: AbortSignal.timeout(30_000),
      headers: { "accept-encoding": "identity" },
      ...(url.protocol === "https:" ? { rejectUnauthorized: true } : {}),
    }, response => {
      const chunks = [];
      response.on("data", chunk => chunks.push(chunk));
      response.on("error", reject);
      response.on("end", () => resolveResponse({
        status: response.statusCode,
        headers: response.headers,
        body: Buffer.concat(chunks),
      }));
    });
    pending.on("error", reject);
    pending.end();
  });
}

const [systemAddresses, ipv4, ipv6] = await Promise.all([
  lookup(hostname, { all: true }), resolve4(hostname), resolve6(hostname),
]);
assert(systemAddresses.length && ipv4.length && ipv6.length, "System DNS, A, and AAAA must resolve.");
console.log("PASS ordinary DNS resolves: " + JSON.stringify({ systemAddresses, ipv4, ipv6 }));

for (const pathname of ["/", "/index.html", "/?group=8"]) {
  const response = await get(siteURL + pathname);
  assert.equal(response.status, 200, "HTTPS " + pathname + " should serve the page.");
  assert.match(response.headers["content-type"] ?? "", /^text\/html\b/i);
  assert.equal(digest(response.body), expectedHash, "HTTPS " + pathname + " must match dist/index.html.");
}
console.log("PASS trusted HTTPS serves the exact artifact at /, /index.html, and /?group=8: " + expectedHash);

const robots = await get(siteURL + "/robots.txt");
assert.equal(robots.status, 200, "HTTPS /robots.txt should be public.");
assert.match(robots.headers["content-type"] ?? "", /^text\/plain\b/i);
assert.equal(digest(robots.body), expectedRobotsHash, "HTTPS /robots.txt must match dist/robots.txt.");
assert.match(robots.body.toString("utf8"), /^User-agent:\s*\*$/m);
assert.match(robots.body.toString("utf8"), /^Allow:\s*\/$/m);
console.log("PASS robots.txt serves the exact permissive crawler policy: " + expectedRobotsHash);

for (const pathname of ["/", "/?group=8", "/robots.txt"]) {
  const response = await get("http://" + hostname + pathname);
  assert.equal(response.status, 301, "HTTP " + pathname + " should redirect permanently.");
  assert.equal(new URL(response.headers.location, "http://" + hostname).href, siteURL + pathname);
}
console.log("PASS HTTP 301 redirects the essay and robots.txt to HTTPS and preserves the group query. URL fragments are browser-side; test #carry in a browser.");

const anonymous = await get("https://reptends-mikedotexe-com-341982967115.s3.us-east-1.amazonaws.com/index.html");
assert.equal(anonymous.status, 403, "The S3 object must remain private.");
const anonymousRobots = await get("https://reptends-mikedotexe-com-341982967115.s3.us-east-1.amazonaws.com/robots.txt");
assert.equal(anonymousRobots.status, 403, "The S3 robots.txt object must remain private.");
console.log("PASS anonymous S3 access is denied for both public CloudFront objects (403).");
