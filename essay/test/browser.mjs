import assert from "node:assert/strict";
import { mkdir, readFile } from "node:fs/promises";
import { createServer } from "node:http";
import { createRequire } from "node:module";
import { dirname, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { recurrenceTrace } from "../src/math/lifts.ts";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const require = createRequire(import.meta.url);
let playwright;
try {
  playwright = process.env.PLAYWRIGHT_MODULE_PATH
    ? await import(pathToFileURL(require.resolve(process.env.PLAYWRIGHT_MODULE_PATH)).href)
    : await import("playwright");
} catch {
  throw new Error("Browser QA needs Playwright. Install it locally or set PLAYWRIGHT_MODULE_PATH to an existing Playwright module.");
}

const pageURL = pathToFileURL(resolve(root, "dist/index.html")).href;
const screenshots = resolve(root, "qa");
await mkdir(screenshots, { recursive: true });
const engine = process.env.BROWSER_ENGINE ?? "chromium";
assert(["chromium", "firefox", "webkit"].includes(engine), "BROWSER_ENGINE must be chromium, firefox, or webkit.");
const browser = await playwright[engine].launch({ headless: true, timeout: 30000 });
const screenshotPath = name => resolve(screenshots, engine === "chromium" ? name : `${engine}-${name}`);
console.log(`Testing ${engine} ${browser.version()}${engine === "webkit" ? " (Safari engine; not the native Safari application)" : ""}.`);
const artifact = await readFile(resolve(root, "dist/index.html"));
const server = createServer((request, response) => {
  response.writeHead(200, { "Content-Type": "text/html; charset=utf-8" });
  response.end(artifact);
});
await new Promise(resolve => server.listen(0, "127.0.0.1", resolve));
const shareTestURL = `http://127.0.0.1:${server.address().port}/`;
const geometric = recurrenceTrace({ base: 1000n, coefficients: [3n] }, 332);

async function loadOfflineArtifact(page) {
  // WebKit's offline emulation rejects file: navigation itself. Load the local
  // file with request monitoring, then disable networking before every control.
  await page.goto(pageURL);
  if (engine === "webkit") await page.context().setOffline(true);
}

async function assertPageFits(page) {
  const dimensions = await page.evaluate(() => ({
    viewport: window.innerWidth,
    content: document.documentElement.scrollWidth,
  }));
  assert(dimensions.content <= dimensions.viewport + 1,
    `The page is ${dimensions.content}px wide in a ${dimensions.viewport}px viewport.`);
}

async function assertPosition(page, index) {
  const expected = geometric.rows[index];
  const actual = await page.evaluate(() => ({
    index: Number(document.querySelector("#position").value),
    raw: document.querySelector("#exact-raw").textContent,
    incoming: document.querySelector("#exact-carry").textContent,
    previous: document.querySelector("#exact-previous").textContent,
    word: document.querySelector("#word-current").textContent,
    remainder: document.querySelector("#orbit-remainder").textContent,
    next: document.querySelector("#local-remainder").textContent,
  }));
  assert.equal(actual.index, index);
  const integer = text => BigInt(text.replace(/[\s,]/g, ""));
  assert.equal(integer(actual.raw), expected.raw);
  assert.equal(integer(actual.incoming), expected.carryIn);
  assert.equal(integer(actual.previous), expected.quotient);
  assert.equal(integer(actual.word), expected.word);
  assert.equal(integer(actual.remainder), expected.remainder);
  assert.equal(integer(actual.next), expected.nextRemainder);
}

async function exerciseControls(page, exhaustive) {
  await page.locator("#reveal").click();
  assert.equal((await page.locator("#hero-answer").textContent()).trim(), "731");
  await assertPosition(page, 6);
  await page.locator("#position").focus();
  await page.locator("#position").press("ArrowRight");
  await assertPosition(page, 7);
  await page.locator("#reset").click();
  await assertPosition(page, 6);
  await page.locator("#cycle-later").click();
  await assertPosition(page, 172);
  assert.match(await page.locator("#power-size").textContent(), /83 digits/);
  await page.locator("#cycle-earlier").click();
  await assertPosition(page, 6);
  await page.locator("#animate-split").click();
  await assertPosition(page, 6);
  const positions = exhaustive ? Array.from({ length: 332 }, (_, index) => index) : [0, 6, 7, 166, 172, 331];
  for (const index of positions) {
    await page.locator("#position").evaluate((element, value) => {
      element.value = String(value);
      element.dispatchEvent(new Event("input", { bubbles: true }));
    }, index);
    await assertPosition(page, index);
  }
  await page.locator("#reset").click();
  const disclosure = page.locator(".geometry-disclosure > summary");
  await disclosure.focus();
  await disclosure.press("Enter");
  assert.equal(await page.locator(".geometry-disclosure").getAttribute("open"), "");
  const geometry = page.locator("#geometry-app");
  await geometry.locator('[data-geometry-mode="square"]').click();
  assert.equal(await geometry.getAttribute("data-mode"), "square");
  await geometry.locator('[data-geometry-action="transform"]').click();
  assert.equal(await geometry.getAttribute("data-view"), "aligned");
  await geometry.locator('[data-geometry-mode="cube"]').click();
  assert.equal(await geometry.getAttribute("data-mode"), "cube");
  await geometry.locator('[data-geometry-action="transform"]').click();
  assert.equal(await geometry.getAttribute("data-view"), "face");
  const selected = Number(await geometry.getAttribute("data-place"));
  assert.equal(Number(await geometry.getAttribute("data-count")), (selected - 1) * (selected - 2) / 2);
  for (const mode of ["square", "cube"]) {
    await geometry.locator(`[data-geometry-mode="${mode}"]`).click();
    const previous = geometry.locator('[data-geometry-action="previous"]');
    const next = geometry.locator('[data-geometry-action="next"]');
    while (!(await previous.isDisabled())) await previous.click();
    assert.equal(await geometry.locator(".geometry-word-zero").count(), mode === "square" ? 1 : 2);
    for (let slice = 0; slice < 6; slice += 1) {
      const place = slice + (mode === "square" ? 2 : 3);
      assert.equal(Number(await geometry.getAttribute("data-place")), place);
      const count = mode === "square" ? place - 1 : (place - 1) * (place - 2) / 2;
      assert.equal(Number(await geometry.getAttribute("data-count")), count);
      if (slice < 5) await next.click();
    }
    assert.equal(await next.isDisabled(), true);
  }
  const angle = geometry.locator("#geometry-angle");
  const priorAngle = Number(await angle.inputValue());
  await angle.focus();
  await angle.press("ArrowRight");
  assert.equal(Number(await angle.inputValue()), priorAngle + 1);
  assert.equal(await geometry.locator('[data-geometry="angle-label"]').textContent(), `${priorAngle + 1}°`);
  await assertPageFits(page);
}

async function exerciseShareLinks() {
  const context = await browser.newContext({
    viewport: { width: 320, height: 1000 },
    reducedMotion: "reduce",
  });
  const errors = [];
  const requests = [];
  await context.addInitScript(() => {
    Object.defineProperty(navigator, "clipboard", {
      configurable: true,
      value: { writeText: async () => { throw new DOMException("Clipboard unavailable", "NotAllowedError"); } },
    });
  });
  const page = await context.newPage();
  page.on("pageerror", error => errors.push(error.message));
  page.on("console", message => {
    if (message.type() === "error") errors.push(message.text());
  });
  page.on("request", request => {
    if (request.url().split(/[?#]/)[0] !== shareTestURL && !request.url().startsWith("data:")) requests.push(request.url());
  });
  for (const [query, index] of [["1", 0], ["332", 331], ["0", 6], ["333", 6], ["3.5", 6], ["nonsense", 6], ["-1", 6], ["2e2", 6], ["", 6]]) {
    await page.goto(`${shareTestURL}?group=${query}#carry`);
    await page.locator("html.js").waitFor();
    await assertPosition(page, index);
  }
  await page.goto(`${shareTestURL}?group=8#carry`);
  await assertPosition(page, 7);
  await page.locator("#next").click();
  await assertPosition(page, 8);
  await page.locator("#next").click();
  await assertPosition(page, 9);
  assert.equal(new URL(page.url()).search, "?group=10");
  assert.equal(new URL(page.url()).hash, "#carry");
  await page.goto(`${shareTestURL}?group=20#carry`);
  await page.locator("#previous").click();
  await assertPosition(page, 18);
  await page.goBack();
  await page.waitForFunction(() => document.querySelector("#position").value === "9");
  await assertPosition(page, 9);
  await page.goForward();
  await page.waitForFunction(() => document.querySelector("#position").value === "18");
  await assertPosition(page, 18);
  await page.locator("#share-position").focus();
  await page.locator("#share-position").press("Enter");
  const fallback = page.locator("#share-link");
  await fallback.waitFor({ state: "visible" });
  assert.equal(await fallback.inputValue(), "https://reptends.mikedotexe.com/?group=19#carry");
  assert.equal(await fallback.getAttribute("readonly"), "");
  const selection = await fallback.evaluate(input => ({
    focused: document.activeElement === input,
    start: input.selectionStart,
    end: input.selectionEnd,
    length: input.value.length,
  }));
  assert.equal(selection.focused, true);
  assert.equal(selection.start, 0);
  assert.equal(selection.end, selection.length);
  await assertPageFits(page);
  await page.screenshot({ path: screenshotPath("320-share-fallback.png") });
  await page.locator("#reset").click();
  await page.locator("#share-position").click();
  await fallback.waitFor({ state: "visible" });
  assert.equal(await fallback.inputValue(), "https://reptends.mikedotexe.com/?group=7#carry");
  assert.deepEqual(errors, [], "Share links and query parsing must not produce browser errors.");
  assert.deepEqual(requests, [], "Sharing a group must not make external requests.");
  await context.close();

  const copyContext = await browser.newContext();
  await copyContext.addInitScript(() => {
    Object.defineProperty(navigator, "clipboard", {
      configurable: true,
      value: { writeText: async value => { window.__copiedURL = value; } },
    });
  });
  const copyPage = await copyContext.newPage();
  await copyPage.goto(`${shareTestURL}?group=332#carry`);
  await copyPage.locator("#share-position").click();
  await copyPage.waitForFunction(() => typeof window.__copiedURL === "string");
  assert.equal(await copyPage.evaluate(() => window.__copiedURL), "https://reptends.mikedotexe.com/?group=332#carry");
  assert.equal(await copyPage.locator("#share-link").isVisible(), false);
  await copyContext.close();
  console.log(`PASS ${engine} share links: initial/boundary/invalid groups, Back/Forward, clipboard success and keyboard-selectable fallback, no requests or errors.`);
}

try {
  await exerciseShareLinks();
  for (const width of engine === "chromium" ? [320, 360, 768, 1440] : [320, 768, 1440]) {
    for (const colorScheme of engine === "chromium" ? ["light", "dark"] : ["light"]) {
      const context = await browser.newContext({
        viewport: { width, height: 1000 },
        colorScheme,
        reducedMotion: "reduce",
        offline: engine !== "webkit",
      });
      const page = await context.newPage();
      const errors = [];
      const requests = [];
      page.on("pageerror", error => errors.push(error.message));
      page.on("console", message => {
        if (message.type() === "error") errors.push(message.text());
      });
      page.on("request", request => {
        if (request.url() !== pageURL && !request.url().startsWith("data:")) requests.push(request.url());
      });
      await loadOfflineArtifact(page);
      await page.getByRole("heading", { level: 1 }).waitFor();
      await assertPageFits(page);
      if ([320, 768].includes(width) && colorScheme === "light") {
        await page.screenshot({ path: screenshotPath(`${width}-top.png`) });
      }
      await exerciseControls(page, engine === "chromium" && width === 1440 && colorScheme === "light");
      await page.screenshot({ path: screenshotPath(`${width}-${colorScheme}.png`), fullPage: true });
      if (width === 320 && colorScheme === "light") {
        await page.locator("#position").evaluate(element => {
          element.value = "331";
          element.dispatchEvent(new Event("input", { bubbles: true }));
        });
        await page.locator("details").evaluateAll(elements => elements.forEach(element => { element.open = true; }));
        await assertPosition(page, 331);
        await assertPageFits(page);
        await page.locator("#exact-raw").scrollIntoViewIfNeeded();
        await page.screenshot({ path: screenshotPath("320-large-values.png") });
      }
      assert.deepEqual(errors, [], "The page must have no runtime or console errors.");
      assert.deepEqual(requests, [], "The single HTML artifact must load without additional requests.");
      await context.close();
      console.log(`PASS ${engine} ${width}px ${colorScheme}: ${engine === "webkit" ? "local file with offline interaction" : "offline load"}, exact controls, keyboard, geometry, layout bounds, no runtime errors.`);
    }
  }

  const fallback = await browser.newContext({
    viewport: { width: 320, height: 1000 },
    javaScriptEnabled: false,
    offline: engine !== "webkit",
  });
  const fallbackPage = await fallback.newPage();
  await loadOfflineArtifact(fallbackPage);
  assert.equal((await fallbackPage.locator("#hero-answer").textContent()).trim(), "731");
  for (const selector of ["#reveal", "#previous", "#animate-split", "#cycle-later"]) {
    assert.equal(await fallbackPage.locator(selector).isVisible(), false, `${selector} should be hidden when JavaScript is disabled.`);
  }
  assert.match(await fallbackPage.locator("#carry-equation").textContent(), /729 \+ 2/);
  await fallbackPage.locator(".geometry-disclosure > summary").click();
  assert.equal(await fallbackPage.locator(".geometry-static").isVisible(), true);
  assert.match(await fallbackPage.locator(".geometry-static").textContent(), /0000, 0000, 0001, 0003/);
  await assertPageFits(fallbackPage);
  await fallbackPage.screenshot({ path: screenshotPath("320-no-javascript.png"), fullPage: true });
  await fallback.close();
  console.log(`PASS ${engine} 320px without JavaScript: readable examples, hidden inactive controls, native disclosures, layout bounds.`);

  const motionContext = await browser.newContext({
    viewport: { width: 1024, height: 1000 },
    reducedMotion: "no-preference",
    offline: engine !== "webkit",
  });
  const motionPage = await motionContext.newPage();
  const motionErrors = [];
  motionPage.on("pageerror", error => motionErrors.push(error.message));
  await loadOfflineArtifact(motionPage);
  const split = motionPage.locator("#animate-split");
  await split.click();
  await motionPage.waitForFunction(() => {
    const moving = document.querySelector('#split-svg rect[fill="#e6d3b1"]');
    const y = Number(moving?.getAttribute("y"));
    return y > 22 && y < 99;
  });
  assert.equal(await split.getAttribute("aria-disabled"), "true");
  await motionPage.waitForFunction(() => document.querySelector("#animate-split").getAttribute("aria-disabled") !== "true");
  assert.equal(await motionPage.locator('#split-svg rect[fill="#e6d3b1"]').first().getAttribute("y"), "99");
  await split.click();
  await motionPage.waitForFunction(() => document.querySelector("#animate-split").getAttribute("aria-disabled") === "true");
  await motionPage.locator("#next").click();
  await assertPosition(motionPage, 7);
  assert.equal(await split.getAttribute("aria-disabled"), null);
  const cancelledDrawing = await motionPage.locator("#split-svg").innerHTML();
  await motionPage.waitForTimeout(1050);
  assert.equal(await motionPage.locator("#split-svg").innerHTML(), cancelledDrawing, "Changing selection must cancel the old split animation.");
  await motionPage.locator("#reset").click();
  await split.click();
  await motionPage.waitForFunction(() => document.querySelector("#animate-split").getAttribute("aria-disabled") !== "true");
  assert.equal(await motionPage.locator('#split-svg rect[fill="#e6d3b1"]').first().getAttribute("y"), "99");
  await motionPage.locator(".geometry-disclosure > summary").click();
  const movingGeometry = motionPage.locator("#geometry-app");
  await movingGeometry.locator('[data-geometry-action="transform"]').click();
  await motionPage.waitForFunction(() => document.querySelector("#geometry-app").dataset.view === "moving");
  await motionPage.waitForFunction(() => document.querySelector("#geometry-app").dataset.view === "aligned");
  await movingGeometry.locator('[data-geometry-mode="cube"]').click();
  await movingGeometry.locator('[data-geometry-action="transform"]').click();
  await motionPage.waitForFunction(() => document.querySelector("#geometry-app").dataset.view === "moving");
  await motionPage.waitForFunction(() => document.querySelector("#geometry-app").dataset.view === "face");
  await assertPageFits(motionPage);
  assert.deepEqual(motionErrors, []);
  await motionContext.close();
  console.log(`PASS ${engine} normal motion: visible split movement, finish/restart, cancellation on selection, square and cube animation completion.`);
} finally {
  await browser.close();
  await new Promise(resolve => server.close(resolve));
}
