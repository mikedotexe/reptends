import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { lookup as nativeLookup } from "node:dns";
import { Resolver } from "node:dns/promises";
import { mkdir, readFile } from "node:fs/promises";
import { request as httpRequest } from "node:http";
import { request as httpsRequest } from "node:https";
import { createRequire } from "node:module";
import { dirname, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const siteURL = "https://reptends.mikedotexe.com/";
const siteHostname = new URL(siteURL).hostname;
const privateObjectURL = "https://reptends-mikedotexe-com-341982967115.s3.us-east-1.amazonaws.com/index.html";
const privateRobotsURL = "https://reptends-mikedotexe-com-341982967115.s3.us-east-1.amazonaws.com/robots.txt";
const digest = value => createHash("sha256").update(value).digest("hex");
let siteAddress;
if (process.env.REPTENDS_DNS_SERVER) {
  const resolver = new Resolver({ timeout: 5000, tries: 2 });
  resolver.setServers([process.env.REPTENDS_DNS_SERVER]);
  const addresses = await resolver.resolve4(siteHostname);
  assert(addresses.length > 0, "The selected DNS server returned no IPv4 address.");
  siteAddress = addresses[0];
  console.log(`Using process-scoped DNS from ${process.env.REPTENDS_DNS_SERVER}: ${siteHostname} → ${siteAddress}. Hostname and TLS verification remain unchanged.`);
}

function lookup(hostname, options, callback) {
  if (hostname !== siteHostname || !siteAddress) return nativeLookup(hostname, options, callback);
  if (options.all) callback(null, [{ address: siteAddress, family: 4 }]);
  else callback(null, siteAddress, 4);
}

function get(address) {
  const url = new URL(address);
  return new Promise((resolveResponse, reject) => {
    const request = url.protocol === "https:" ? httpsRequest : httpRequest;
    const requestOptions = {
      agent: false,
      signal: AbortSignal.timeout(30_000),
      headers: { "accept-encoding": "identity" },
      ...(siteAddress ? { lookup } : {}),
      // The URL still supplies the real Host header; SNI and certificate checks
      // also use that hostname, even when the connection uses a resolved IP.
      ...(url.protocol === "https:" ? { servername: url.hostname, rejectUnauthorized: true } : {}),
    };
    const pending = request(url, requestOptions, response => {
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

for (const pathname of ["", "robots.txt"]) {
  const source = new URL(pathname, "http://reptends.mikedotexe.com/");
  const destination = new URL(pathname, siteURL);
  const http = await get(source);
  assert([301, 302, 307, 308].includes(http.status), `HTTP ${source.pathname} should redirect; received ${http.status}.`);
  assert.equal(new URL(http.headers.location, source).href, destination.href);
}
console.log("PASS the essay and robots.txt redirect from HTTP to HTTPS.");

const published = await get(siteURL);
assert.equal(published.status, 200);
assert.match(published.headers["content-type"] ?? "", /^text\/html\b/i);
const expectedHash = digest(await readFile(resolve(root, "dist/index.html")));
assert.equal(digest(published.body), expectedHash);
console.log(`PASS HTTPS serves the exact local artifact (${expectedHash}).`);

const expectedRobots = await readFile(resolve(root, "dist/robots.txt"));
const robots = await get(new URL("robots.txt", siteURL));
assert.equal(robots.status, 200);
assert.match(robots.headers["content-type"] ?? "", /^text\/plain\b/i);
assert.equal(digest(robots.body), digest(expectedRobots));
assert.match(robots.body.toString("utf8"), /^User-agent:\s*\*$/m);
assert.match(robots.body.toString("utf8"), /^Allow:\s*\/$/m);
console.log("PASS robots.txt serves the exact permissive crawler policy.");

const anonymous = await get(privateObjectURL);
assert.equal(anonymous.status, 403, `Anonymous S3 access should be denied; received ${anonymous.status}.`);
const anonymousRobots = await get(privateRobotsURL);
assert.equal(anonymousRobots.status, 403, `Anonymous S3 robots.txt access should be denied; received ${anonymousRobots.status}.`);
console.log("PASS anonymous S3 access is denied for index.html and robots.txt (403).");

const require = createRequire(import.meta.url);
let playwright;
try {
  playwright = process.env.PLAYWRIGHT_MODULE_PATH
    ? await import(pathToFileURL(require.resolve(process.env.PLAYWRIGHT_MODULE_PATH)).href)
    : await import("playwright");
} catch {
  throw new Error("Live browser QA needs Playwright. Install it locally or set PLAYWRIGHT_MODULE_PATH to an existing Playwright module.");
}

const browser = await playwright.chromium.launch({
  headless: true,
  ...(siteAddress ? { args: [`--host-resolver-rules=MAP ${siteHostname} ${siteAddress}`] } : {}),
});
try {
  // Certificate errors remain fatal: do not set ignoreHTTPSErrors here.
  const context = await browser.newContext({ viewport: { width: 1440, height: 1000 }, reducedMotion: "reduce" });
  const page = await context.newPage();
  const errors = [];
  const subresources = [];
  page.on("pageerror", error => errors.push(error.message));
  page.on("console", message => {
    if (message.type() === "error") errors.push(message.text());
  });
  page.on("request", request => {
    if (request.url() !== siteURL && !request.url().startsWith("data:")) subresources.push(request.url());
  });
  const navigation = await page.goto(siteURL);
  assert.equal(navigation?.status(), 200);
  assert.equal(page.url(), siteURL);
  await page.locator("#reveal").click();
  assert.equal((await page.locator("#hero-answer").textContent()).trim(), "731");
  await page.locator("#next").click();
  assert.equal((await page.locator("#word-current").textContent()).trim(), "193");
  await page.locator("#reset").click();
  assert.equal((await page.locator("#word-current").textContent()).trim(), "731");
  await page.locator("#cycle-later").click();
  assert.equal(await page.locator("#position").inputValue(), "172");
  assert.equal((await page.locator("#word-current").textContent()).trim(), "731");
  assert.match(await page.locator("#power-size").textContent(), /83 digits/);
  for (const [index, printed] of [[55, "700"], [165, "667"], [6, "731"]]) {
    await page.locator(`[data-boundary-position="${index}"]`).click();
    assert.equal(await page.locator("#position").inputValue(), String(index));
    assert.equal(await page.locator("#orbit-word").textContent(), printed);
  }
  await page.locator("#boundary-comparison > summary").click();
  assert.equal(await page.locator(".boundary-table tbody tr").count(), 4);
  await page.locator("#boundary-comparison > summary").click();
  await page.locator(".geometry-disclosure > summary").click();
  const geometry = page.locator("#geometry-app");
  await geometry.locator('[data-geometry-mode="cube"]').click();
  assert.equal(await geometry.getAttribute("data-mode"), "cube");
  await geometry.locator('[data-geometry-action="transform"]').click();
  assert.equal(await geometry.getAttribute("data-view"), "face");
  assert.deepEqual(subresources, [], "The published page should make no additional asset requests.");
  assert.deepEqual(errors, [], "The published page should have no browser errors.");
  await page.locator("#reset").click();
  await page.evaluate(() => window.scrollTo({ top: 0, behavior: "instant" }));
  const screenshot = resolve(root, "qa/live-desktop.png");
  await mkdir(dirname(screenshot), { recursive: true });
  await page.screenshot({ path: screenshot });
  console.log("PASS live browser: trusted TLS, reveal, next/reset, 166-group return, cube controls, no additional requests or errors.");
  console.log(`Saved ${screenshot}`);
  await context.close();
} finally {
  await browser.close();
}
