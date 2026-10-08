import assert from "node:assert/strict";
import { mkdir, readFile } from "node:fs/promises";
import { createServer } from "node:http";
import { createRequire } from "node:module";
import { dirname, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { formatWord, recurrenceTrace } from "../src/math/lifts.ts";

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

async function setDisclosure(page, selector, open) {
  const disclosure = page.locator(selector);
  if (await disclosure.evaluate(element => element.open) !== open) {
    const summary = disclosure.locator(":scope > summary");
    await summary.focus();
    await summary.press("Enter");
  }
  assert.equal(await disclosure.evaluate(element => element.open), open);
}

async function assertReadingStructure(page) {
  for (const selector of ["#carry-inspector", "#split-note", "#ternary-note", "#verification-guide"]) {
    assert.equal(await page.locator(selector).evaluate(element => element.open), false,
      `${selector} should start as an optional native disclosure.`);
  }
  for (const selector of ["#comparison", "#split-svg", "#orbit-digit"]) {
    assert.equal(await page.locator(selector).isVisible(), false, `${selector} belongs to a collapsed deeper explanation.`);
  }
  assert.equal(await page.locator("#repeat #orbit-readouts #position").count(), 1);
  assert.equal(await page.locator("#repeat .orbit-readout > div").count(), 3);
  for (const selector of ["#orbit-power", "#orbit-remainder", "#orbit-word", "#ordinary-equation", "#orbit-next"]) {
    assert.equal(await page.locator(selector).isVisible(), true, `${selector} must remain in the main reading path.`);
  }
  assert.deepEqual(await page.locator(".chapter-nav a").evaluateAll(links => links.map(link => link.getAttribute("href"))),
    ["#carry", "#repeat", "#soft-end", "#research"]);
  assert.equal(await page.locator("#repeat").evaluate(element => element.nextElementSibling?.id), "soft-end",
    "The finite-description chapter should follow the remainder explorer.");
}

async function assertVerificationGuide(page, interactive = true) {
  const record = page.locator("script#reptends-certificate");
  assert.equal(await record.count(), 1);
  assert.equal(await record.getAttribute("type"), "application/json");
  const certificate = JSON.parse(await record.textContent());
  assert.equal(certificate.schema_version, 1);
  assert.deepEqual(certificate.cases.map(item => [
    item.denominator, item.word_width,
    item.decimal.preperiod_length, item.decimal.period_length,
    item.grouped.preperiod_length, item.grouped.period_length,
    item.first_incoming_carry.word_index,
    item.decimal.endpoint.word_index, item.decimal.endpoint.containing_word,
    item.grouped.endpoint.word_index, item.grouped.endpoint.word,
  ]), [
    ["97", 2, 0, 96, 0, 48, 4, 47, "67", 47, "67"],
    ["997", 3, 0, 166, 0, 166, 6, 55, "700", 165, "667"],
    ["94", 2, 1, 46, 1, 23, 2, 23, "51", 23, "51"],
    ["994", 3, 1, 210, 1, 70, 3, 70, "501", 70, "501"],
  ]);
  const guide = page.locator("#verification-guide");
  if (interactive) {
    const link = page.locator('#carry a[href="#verification-guide"]');
    await link.focus();
    await link.press("Enter");
    await page.waitForFunction(() => document.querySelector("#verification-guide").open);
    assert.equal(new URL(page.url()).hash, "#verification-guide");
  } else {
    await setDisclosure(page, "#verification-guide", true);
  }
  assert.equal(await guide.locator(".verification-code").isVisible(), true);
  assert.equal(await guide.locator(".boundary-table tbody tr").count(), 4);
  await assertPageFits(page);
  await setDisclosure(page, "#verification-guide", false);
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
    baseThreeDigit: document.querySelector("#orbit-digit").textContent,
    orbitWord: document.querySelector("#orbit-word").textContent,
    orbitWordEquation: document.querySelector("#orbit-word-equation").textContent,
    orbitStep: document.querySelector("#orbit-step").textContent,
    ordinaryEquation: document.querySelector("#ordinary-equation").textContent,
    nextInstruction: document.querySelector("#orbit-next").textContent,
    valueText: document.querySelector("#position").getAttribute("aria-valuetext"),
    next: document.querySelector("#local-remainder").textContent,
  }));
  assert.equal(actual.index, index);
  const integer = text => BigInt(text.replace(/[\s,]/g, ""));
  assert.equal(integer(actual.raw), expected.raw);
  assert.equal(integer(actual.incoming), expected.carryIn);
  assert.equal(integer(actual.previous), expected.quotient);
  assert.equal(integer(actual.word), expected.word);
  assert.equal(integer(actual.remainder), expected.remainder);
  const baseThreeDigit = 3n * expected.remainder / 997n;
  assert.equal(integer(actual.baseThreeDigit), baseThreeDigit);
  assert.equal(actual.orbitWord, formatWord(expected.word, 1000n));
  assert.equal(actual.orbitWordEquation, `${expected.remainder} + ${baseThreeDigit} = ${formatWord(expected.word, 1000n)}`);
  assert.equal(actual.orbitStep, `3 × ${expected.remainder} = ${baseThreeDigit} × 997 + ${expected.nextRemainder}`);
  assert.equal(actual.ordinaryEquation, `1000 × ${expected.remainder} = 997 × ${expected.word} + ${expected.nextRemainder}`);
  assert.equal(actual.nextInstruction, `Pass remainder ${expected.nextRemainder} into the next step.`);
  assert.equal(actual.valueText, `Group ${index + 1} of 332: growing power 3 to exponent ${index}, remainder ${expected.remainder}, three-digit word ${formatWord(expected.word, 1000n)}`);
  assert.equal(integer(actual.next), expected.nextRemainder);
}

async function assertOpeningGallery(page) {
  const gallery = page.locator("#specimens");
  const examples = gallery.locator("article.decimal-example");
  assert.equal(await examples.count(), 3);
  const expected = [
    ["97", 4, "27", "81", "83"],
    ["997", 6, "243", "729", "731"],
    ["9997", 8, "2187", "6561", "6562"],
  ];
  for (let index = 0; index < expected.length; index += 1) {
    const [denominator, matchingGroups, lastPower, expectedNext, printedNext] = expected[index];
    const example = examples.nth(index);
    assert.equal(await example.getAttribute("data-denominator"), denominator);
    assert.equal(await example.getByRole("heading").textContent(), `1/${denominator}`);
    const groups = await example.locator(".decimal-group").evaluateAll(elements => elements.map(element => {
      const bounds = element.getBoundingClientRect();
      const parent = element.closest("article").getBoundingClientRect();
      return {
        kind: element.dataset.kind,
        printed: element.textContent,
        word: element.dataset.word,
        visibleWithinExample: bounds.width > 0 && bounds.height > 0 && bounds.left >= parent.left && bounds.right <= parent.right,
      };
    }));
    assert.equal(groups.length, 16, "Each example must show a substantial decimal prefix before the focused explanation.");
    assert.equal(groups.filter(group => group.kind === "pattern").length, matchingGroups);
    assert.equal(groups[matchingGroups].kind, "change");
    assert.equal(groups.filter(group => group.kind === "change").length, 1);
    assert(groups.slice(matchingGroups + 1).every(group => group.kind === "later"));
    for (const group of groups) {
      assert.equal(group.printed, group.word, "The visible digits must preserve the serialized groups, including initial zeros.");
      assert(group.visibleWithinExample, "Every printed group must remain visible inside its example, without clipped overflow.");
    }
    const continuous = (await example.locator(".decimal-expansion").textContent()).trim();
    assert.equal(continuous, "0." + groups.map(group => group.printed).join("") + "…",
      "The introduction must show the actual continuous decimal without inserted spaces.");
    const caption = (await example.locator(".decimal-example-caption").textContent()).replace(/\s+/g, " ").trim();
    assert.equal(caption, `Tripling stays visible through ${lastPower}. Then ${expectedNext} becomes ${printedNext}.`);
  }
  for (const label of ["×3 pattern", "First change", "The “number jumble”"]) {
    assert.equal(await gallery.getByText(label, { exact: true }).isVisible(), true, "Text labels must accompany the gallery colors.");
  }
  assert.equal(await gallery.evaluate(element => Boolean(element.compareDocumentPosition(document.querySelector("#focus-997")) & Node.DOCUMENT_POSITION_FOLLOWING)), true,
    "Readers must encounter the decimal examples before the focused 1/997 explanation.");
  assert.equal((await page.locator("#hero-answer").textContent()).trim(), "731", "The focused explanation must retain the answer already shown in the opening decimals.");
}

async function assertPowerStack(page) {
  const stack = page.locator("#power-stack");
  assert.equal(await stack.getByRole("heading", { name: "The “salad” is simple addition." }).isVisible(), true);
  const table = stack.locator("table.power-stack-table");
  assert.equal(await table.locator("tbody tr").count(), 8);
  assert.deepEqual(await table.locator('tbody tr[data-exponent="7"] td').allTextContents(), ["", "", "002", "187", "", "", "", ""]);
  assert.deepEqual(await table.locator('tbody tr[data-exponent="11"] td').allTextContents(), ["", "", "", "", "", "", "177", "147"]);
  assert.deepEqual(await table.locator("tfoot td").allTextContents(), ["081", "243", "731", "193", "580", "742", "226", "…"]);
  for (const addition of ["729 + 002 = 731", "187 + 006 = 193", "561 + 019 = 580", "683 + 059 = 742", "049 + 177 = 226"]) {
    assert.equal(await stack.getByText(addition, { exact: true }).isVisible(), true);
  }
  const scroller = stack.locator(".power-stack-scroll");
  const scroll = await scroller.evaluate(element => ({ client: element.clientWidth, full: element.scrollWidth }));
  if (scroll.full > scroll.client) {
    const lastCellVisible = await scroller.evaluate(element => {
      element.scrollLeft = element.scrollWidth;
      const viewport = element.getBoundingClientRect();
      const last = element.querySelector("tfoot td:last-child").getBoundingClientRect();
      const visible = last.left >= viewport.left && last.right <= viewport.right + 1;
      element.scrollLeft = 0;
      return visible;
    });
    assert.equal(lastCellVisible, true, "The complete stack must be reachable by horizontal scrolling.");
  }
}

async function assertComparisonTable(page) {
  await setDisclosure(page, "#carry-inspector", true);
  const table = page.locator("#comparison");
  assert.equal(await table.isVisible(), true);
  assert.equal(await table.evaluate(element => getComputedStyle(element).display), "table");
  assert.equal(await table.locator("thead tr").evaluate(element => getComputedStyle(element).display), "table-row");
  assert.equal(await table.locator("tbody tr").first().evaluate(element => getComputedStyle(element).display), "table-row");
  assert.deepEqual((await table.getByRole("columnheader").allTextContents()).map(text => text.trim()), ["Group 6", "Group 7", "Group 8"]);
  assert.deepEqual((await table.getByRole("rowheader").allTextContents()).map(text => text.replace(/\s+/g, " ").trim()), ["Growing termsThe construction", "Printed groupsThe familiar decimal"]);
  assert.equal(await table.locator('thead th[scope="col"]').count(), 3);
  assert.equal(await table.locator('tbody th[scope="row"]').count(), 2);
  assert.equal(await table.locator("tbody td").count(), 6);
  await setDisclosure(page, "#carry-inspector", false);
}

async function assertRepetitionBoundaries(page, interactive = true) {
  const card = page.locator("#soft-end");
  assert.equal(await card.getByRole("heading", { name: "When have we seen enough?" }).isVisible(), true);
  assert.equal(await card.locator(".boundary-landmarks > li").count(), 3);
  assert.equal(await card.locator(".boundary-split").getAttribute("aria-label"), "Word 700: 7 ends the first repetend; 00 starts its next copy");
  if (interactive) {
    for (const [index, word] of [[6, "731"], [55, "700"], [165, "667"]]) {
      const button = card.locator(`[data-boundary-position="${index}"]`);
      await button.focus();
      await button.press("Enter");
      await assertPosition(page, index);
      assert.equal(await page.locator("#orbit-word").textContent(), word);
      assert.equal(await page.evaluate(() => document.activeElement?.id), "orbit-readouts");
      assert.match(await card.locator("#boundary-position").textContent(), new RegExp(`group ${index + 1}`));
    }
    await page.locator("#cycle-later").click();
    await assertPosition(page, 331);
    await page.locator("#reset").click();
    await assertPosition(page, 6);
  } else {
    for (const button of await card.locator("[data-boundary-position]").all()) {
      assert.equal(await button.isVisible(), false, "Jump controls require JavaScript; the examples do not.");
    }
  }
  const summary = page.locator("#boundary-comparison > summary");
  await summary.focus();
  await summary.press("Enter");
  assert.equal(await page.locator("#boundary-comparison").getAttribute("open"), "");
  const table = card.locator(".boundary-table");
  assert.equal(await table.getByRole("columnheader").count(), 5);
  for (const [denominator, period, exponent, count, word, loop] of [
    [97, 96, "347", 48, "67│", 48],
    [997, 166, "355", 56, "7│00", 166],
    [94, 46, "623", 24, "5│1", 23],
    [994, 210, "670", 71, "5│01", 70],
  ]) {
    const cells = await table.locator(`[data-boundary-denominator="${denominator}"] td`).allTextContents();
    assert.match(cells[0], new RegExp(`^${period} repeating digits`));
    assert.match(cells[1], new RegExp(`^${exponent}${count} power positions`));
    assert.equal(cells[2], word);
    assert.match(cells[3], new RegExp(`^${loop} repeating words`));
    if (denominator === 94 || denominator === 994) {
      assert.match(cells[0], /initial nonrepeating 0/);
      assert.match(cells[3], /1 startup word/);
    }
  }
  const scroller = card.locator(".boundary-table-scroll");
  assert.equal(await scroller.evaluate(element => {
    element.scrollLeft = element.scrollWidth;
    const outer = element.getBoundingClientRect();
    const last = element.querySelector("tbody tr:last-child td:last-child").getBoundingClientRect();
    const visible = last.right <= outer.right + 1;
    element.scrollLeft = 0;
    return visible;
  }), true, "All comparison columns must be reachable on mobile.");
  const receiptsSummary = card.locator(".boundary-receipts > summary");
  await receiptsSummary.focus();
  await receiptsSummary.press("Enter");
  assert.equal(await card.locator(".boundary-receipts").getAttribute("open"), "");
  assert.equal(await card.locator(".boundary-receipt").count(), 4);
  await assertPageFits(page);
  await receiptsSummary.press("Enter");
  await summary.focus();
  await summary.press("Enter");
  assert.equal(await page.locator("#boundary-comparison").getAttribute("open"), null);
}

async function exerciseNavigationFocus() {
  const context = await browser.newContext({
    reducedMotion: "reduce",
    offline: engine !== "webkit",
  });
  const page = await context.newPage();
  await loadOfflineArtifact(page);
  const skip = page.locator(".skip-link");
  await skip.focus();
  await skip.press("Enter");
  await page.waitForFunction(() => document.activeElement?.id === "main");
  for (const id of ["carry", "repeat", "soft-end", "research"]) {
    const link = page.locator(`.chapter-nav a[href="#${id}"]`);
    await link.focus();
    await link.press("Enter");
    await page.waitForFunction(target => document.activeElement?.id === target, id);
  }
  await context.close();
  console.log(`PASS ${engine} skip and chapter links move keyboard focus to their destinations.`);
}

async function exerciseControls(page, exhaustive) {
  await page.locator("#reveal").focus();
  await page.locator("#reveal").press("Enter");
  assert.equal((await page.locator("#hero-answer").textContent()).trim(), "731");
  assert.equal(await page.evaluate(() => document.activeElement?.id), "carry", "The explanation button must move keyboard focus to the carry section.");
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
  await setDisclosure(page, "#split-note", true);
  await page.locator("#animate-split").click();
  await assertPosition(page, 6);
  await setDisclosure(page, "#split-note", false);
  await setDisclosure(page, "#ternary-note", true);
  assert.equal(await page.locator("#orbit-digit").isVisible(), true);
  assert.equal(await page.locator("#orbit-step").isVisible(), true);
  assert.equal(await page.locator("#whole-power").isVisible(), true);
  await setDisclosure(page, "#ternary-note", false);
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
  assert.equal(await fallback.inputValue(), "https://reptends.mikedotexe.com/?group=19#repeat");
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
  assert.equal(await fallback.inputValue(), "https://reptends.mikedotexe.com/?group=7#repeat");
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
  assert.equal(await copyPage.evaluate(() => window.__copiedURL), "https://reptends.mikedotexe.com/?group=332#repeat");
  assert.equal(await copyPage.locator("#share-link").isVisible(), false);
  await copyPage.goto(`${shareTestURL}?group=56#repeat`);
  await assertPosition(copyPage, 55);
  assert.equal(new URL(copyPage.url()).hash, "#repeat");
  await copyPage.goto(`${shareTestURL}#verification-guide`);
  await copyPage.waitForFunction(() => document.querySelector("#verification-guide").open);
  assert.equal(await copyPage.locator("#verification-guide .verification-code").isVisible(), true);
  await copyContext.close();
  console.log(`PASS ${engine} share links: initial/boundary/invalid groups, Back/Forward, clipboard success and keyboard-selectable fallback, no requests or errors.`);
}

try {
  await exerciseShareLinks();
  await exerciseNavigationFocus();
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
      await assertReadingStructure(page);
      await assertOpeningGallery(page);
      await assertPowerStack(page);
      await assertComparisonTable(page);
      if ([320, 768].includes(width) && colorScheme === "light") {
        await page.screenshot({ path: screenshotPath(`${width}-top.png`) });
      }
      if ([320, 768, 1440].includes(width) && colorScheme === "light") {
        await page.locator("#specimens").screenshot({ path: screenshotPath(`${width}-opening-gallery.png`) });
      }
      if ([320, 1440].includes(width) && colorScheme === "light") {
        await page.locator("#power-stack").screenshot({ path: screenshotPath(`${width}-power-stack.png`) });
      }
      await exerciseControls(page, engine === "chromium" && width === 1440 && colorScheme === "light");
      await assertRepetitionBoundaries(page);
      await assertVerificationGuide(page);
      if ([320, 768, 1440].includes(width) && colorScheme === "light") {
        await page.locator("#soft-end").screenshot({ path: screenshotPath(`${width}-soft-end.png`) });
      }
      if ([320, 1440].includes(width) && colorScheme === "light") {
        await page.locator(".orbit-card").screenshot({ path: screenshotPath(`${width}-three-views.png`) });
      }
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
    reducedMotion: "reduce",
    offline: engine !== "webkit",
  });
  const fallbackPage = await fallback.newPage();
  await loadOfflineArtifact(fallbackPage);
  await assertReadingStructure(fallbackPage);
  await assertOpeningGallery(fallbackPage);
  await assertPowerStack(fallbackPage);
  await assertComparisonTable(fallbackPage);
  await assertRepetitionBoundaries(fallbackPage, false);
  await assertVerificationGuide(fallbackPage, false);
  assert.equal((await fallbackPage.locator("#hero-answer").textContent()).trim(), "731");
  for (const selector of ["#reveal", "#previous", "#animate-split", "#cycle-later"]) {
    assert.equal(await fallbackPage.locator(selector).isVisible(), false, `${selector} should be hidden when JavaScript is disabled.`);
  }
  assert.match(await fallbackPage.locator("#carry-equation").textContent(), /729 \+ 2/);
  assert.equal((await fallbackPage.locator("#ordinary-equation").textContent()).trim(), "1000 × 729 = 997 × 731 + 193");
  await setDisclosure(fallbackPage, "#ternary-note", true);
  assert.equal((await fallbackPage.locator("#orbit-digit").textContent()).trim(), "2");
  assert.equal((await fallbackPage.locator("#orbit-word").textContent()).trim(), "731");
  assert.match(await fallbackPage.locator("#orbit-step").textContent(), /3 × 729 = 2 × 997 \+ 193/);
  await setDisclosure(fallbackPage, "#ternary-note", false);
  await setDisclosure(fallbackPage, "#split-note", true);
  assert.equal(await fallbackPage.locator("#split-svg").isVisible(), true);
  await setDisclosure(fallbackPage, "#split-note", false);
  await fallbackPage.locator(".geometry-disclosure > summary").click();
  assert.equal(await fallbackPage.locator(".geometry-static").isVisible(), true);
  assert.match(await fallbackPage.locator(".geometry-static").textContent(), /0000, 0000, 0001, 0003/);
  await assertPageFits(fallbackPage);
  await fallbackPage.screenshot({ path: screenshotPath("320-no-javascript.png"), fullPage: true });
  await fallbackPage.locator("#specimens").screenshot({ path: screenshotPath("320-opening-gallery-no-javascript.png") });
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
  await setDisclosure(motionPage, "#split-note", true);
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
