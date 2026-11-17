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

import { assertProgression } from "./progression-browser.mjs";

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
  for (const selector of ["#carry-inspector", "#split-note", "#ternary-note", "#verification-guide"]) {
    assert.equal(await page.locator(selector).evaluate(element => element.open), false);
  }
  assert.equal(await page.locator("#repeat .orbit-readout > div").count(), 3);
  assert.equal(await page.locator("#repeat #orbit-readouts #position").count(), 1);
  assert.equal((await page.locator("#ordinary-equation").textContent()).trim(), "1000 × 729 = 997 × 731 + 193");
  await page.locator("#reveal").click();
  assert.equal((await page.locator("#hero-answer").textContent()).trim(), "731");
  await page.locator("#next").click();
  assert.equal((await page.locator("#orbit-word").textContent()).trim(), "193");
  assert.equal((await page.locator("#ordinary-equation").textContent()).trim(), "1000 × 193 = 997 × 193 + 579");
  assert.equal((await page.locator("#orbit-next").textContent()).trim(), "Pass remainder 579 into the next step.");
  await page.locator("#reset").click();
  assert.equal((await page.locator("#orbit-word").textContent()).trim(), "731");
  await page.locator("#cycle-later").click();
  assert.equal(await page.locator("#position").inputValue(), "172");
  assert.equal((await page.locator("#orbit-word").textContent()).trim(), "731");
  assert.equal((await page.locator("#ordinary-equation").textContent()).trim(), "1000 × 729 = 997 × 731 + 193");
  assert.match(await page.locator("#power-size").textContent(), /83 digits/);
  for (const [index, printed] of [[55, "700"], [165, "667"], [6, "731"]]) {
    await page.locator(`[data-boundary-position="${index}"]`).click();
    assert.equal(await page.locator("#position").inputValue(), String(index));
    assert.equal(await page.locator("#orbit-word").textContent(), printed);
    if (index === 55) {
      assert.equal(await page.locator("#orbit-boundary").isVisible(), true);
      assert.equal(await page.locator("#orbit-word .decimal-word-before").textContent(), "7");
      assert.equal(await page.locator("#orbit-word .decimal-word-after").textContent(), "00");
      await page.locator("#orbit-boundary summary").press("Enter");
      assert.deepEqual(await page.locator("#orbit-boundary .decimal-step-equation").allTextContents(), [
        "10 × 698 = 997 × 7 + 1", "10 × 1 = 997 × 0 + 10", "10 × 10 = 997 × 0 + 100",
      ]);
      assert.match(await page.locator("#orbit-boundary").textContent(), /step ends with remainder 100/);
    }
  }
  assert.equal(await page.locator("#orbit-boundary").isVisible(), false);
  await page.locator(".chapter-nav a[href='#change-radix']").click();
  for (const example of ["powers", "fibonacci", "counting"]) {
    await page.locator("#hp-" + example).click();
    for (let step = 0; step < 4; step++) {
      await assertProgression(page, example, step);
      if (step < 3) await page.locator("#hp-next").click();
    }
  }
  console.log("PASS live retained progressions: 729,2187,6561,19683; 89,144,233,377; and 998,999,1000,1001 with exact value preservation.");
  assert.equal((await page.locator("#run-digit").textContent()).trim(), "27");
  await page.locator("#run-from-start > summary").click();
  await page.locator("#run-166").click();
  assert.equal(await page.locator("#run-position").inputValue(), "166");
  assert.equal(await page.locator("#run-digit").getAttribute("data-exact"), String(3n ** 166n));
  assert.equal(await page.locator("#run-radix").getAttribute("data-exact"), String(997n * 3n ** 166n + 1n));
  await page.locator("#run-next").click();
  assert.equal(await page.locator("#run-digit").getAttribute("data-exact"), String(3n ** 167n));
  await page.locator("#run-start").click();
  await page.locator("#run-from-start > summary").click();
  await page.locator(".chapter-nav a[href='#digit-index']").click();
  await page.locator('[data-di-preset="return"]').click();
  assert.equal(await page.locator("#di-tape").textContent(), "001");
  assert.match(await page.locator("#di-result-base").textContent(), /Base 1000/);
  assert.match(await page.locator("#di-result-note").textContent(), /not an individual decimal-place number/);
  await page.locator("#di-power-bridge > summary").click();
  assert.equal(await page.locator("#di-full-power").textContent(), `3^166 = ${3n ** 166n}`);
  assert.equal(await page.locator("#di-power-quotient").textContent(), String(3n ** 166n / 997n));
  assert.equal(await page.locator("#di-power-carry").textContent(), String(3n ** 167n / 997n));
  await page.locator("#di-check-start").click();
  await page.waitForFunction(() => document.getElementById("di-check-status").textContent.startsWith("Confirmed."));
  assert.match(await page.locator("#di-check-status").textContent(), /entering remainder and all 1 requested digit/);
  const digitIndexScreenshot = resolve(root, "qa/live-digit-index.png");
  await mkdir(dirname(digitIndexScreenshot), { recursive: true });
  await page.locator("#digit-index").screenshot({ path: digitIndexScreenshot });
  await page.locator("#di-power-bridge > summary").click();
  await page.locator('[data-di-preset="huge"]').click();
  assert.equal(await page.locator("#di-tape").textContent(), "6");
  assert.match(await page.locator("#di-result-title").textContent(), /10\^100/);
  assert.equal(await page.locator("#di-check-start").isDisabled(), true);
  assert.match(await page.locator("#di-check-help").textContent(), /limits a sequential check to position 100000/);
  await page.locator('[data-di-preset="start"]').click();
  assert.equal(await page.locator("#di-from").inputValue(), "1");
  assert.equal(await page.locator("#di-to").inputValue(), "60");
  assert.equal((await page.locator("#di-tape").textContent()).length, 60);
  assert.equal(await page.locator("#di-error").isVisible(), false);
  console.log("PASS live indexed digits: group 167 = 001, full 3^166 and carries, independent sequential check, and 1/9899 at position 10^100 = 6.");
  console.log(`Saved ${digitIndexScreenshot}`);
  await page.locator("#boundary-comparison > summary").click();
  assert.equal(await page.locator("#boundary-comparison .boundary-table tbody tr").count(), 4);
  await page.locator("#boundary-comparison > summary").click();
  for (const [selector, visible] of [["#carry-inspector", "#comparison"], ["#split-note", "#split-svg"], ["#ternary-note", "#orbit-digit"]]) {
    const summary = page.locator(`${selector} > summary`);
    await summary.focus();
    await summary.press("Enter");
    assert.equal(await page.locator(visible).isVisible(), true);
    if (selector === "#split-note") await page.locator("#animate-split").click();
    await summary.focus();
    await summary.press("Enter");
    assert.equal(await page.locator(selector).evaluate(element => element.open), false);
  }
  const certificateElement = page.locator("script#reptends-certificate");
  assert.equal(await certificateElement.count(), 1);
  assert.equal(await certificateElement.getAttribute("type"), "application/json");
  const certificate = JSON.parse(await certificateElement.textContent());
  assert.equal(certificate.schema_version, 1);
  assert.deepEqual(certificate.cases.map(item => [
    item.denominator, item.decimal.period_length, item.grouped.period_length,
    item.decimal.endpoint.word_index, item.decimal.endpoint.containing_word,
    item.grouped.endpoint.word_index, item.grouped.endpoint.word,
  ]), [
    ["97", 96, 48, 47, "67", 47, "67"],
    ["997", 166, 166, 55, "700", 165, "667"],
    ["94", 46, 23, 23, "51", 23, "51"],
    ["994", 210, 70, 70, "501", 70, "501"],
  ]);
  await page.getByRole("link", { name: "Check the identity.", exact: true }).click();
  await page.waitForFunction(() => document.querySelector("#verification-guide").open);
  assert.equal(await page.locator("#verification-guide .verification-code").isVisible(), true);
  await page.locator("#verification-guide > summary").click();
  assert.equal(await page.locator("#geometry-app").count(),0);
  const notation=JSON.parse(await page.locator("script#reptends-notation").textContent());
  assert.deepEqual(notation.examples.map(e=>e.denominator),["997","9899","998001"]);
  await page.locator("#notation-reference > summary").click();
  assert.match(await page.locator("#notation-reference").textContent(), /radix_change_preserves_value/);
  await page.locator("#notation-reference > summary").click();
  assert.deepEqual(subresources, [], "The published page should make no additional asset requests.");
  assert.deepEqual(errors, [], "The published page should have no browser errors.");
  await page.locator("#reset").click();
  await page.evaluate(() => window.scrollTo({ top: 0, behavior: "instant" }));
  const screenshot = resolve(root, "qa/live-desktop.png");
  await mkdir(dirname(screenshot), { recursive: true });
  await page.screenshot({ path: screenshot });
  console.log("PASS live browser: trusted TLS, exact three-view explorer, 166-group return, indexed-digit chapter, native disclosures, four-case certificate, verifier link, run notation and proof reference, no additional requests or errors.");
  console.log(`Saved ${screenshot}`);
  await context.close();
} finally {
  await browser.close();
}
