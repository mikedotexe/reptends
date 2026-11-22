import assert from "node:assert/strict";
import { mkdir, readFile } from "node:fs/promises";
import { createServer } from "node:http";
import { createRequire } from "node:module";
import { dirname, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { formatWord, recurrenceTrace } from "../src/math/lifts.ts";
import { assertProgression, exerciseProgression } from "./progression-browser.mjs";
import { exerciseDigitIndex } from "./digit-index-browser.mjs";
import { assertRemainderStory } from "./remainder-story-browser.mjs";
import { assertFieldLesson, exerciseFieldLinks } from "./field-browser.mjs";
import { assertPowerDial, exercisePowerDialLinks } from "./power-dial-browser.mjs";

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
    ["#focus-997", "#carry", "#repeat", "#soft-end", "#one-digit", "#change-radix", "#nearby-fractions", "#power-and-grouping", "#digit-index", "#research"]);
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
    const link = page.getByRole("link", { name: "Check the identity.", exact: true });
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
    boundaryAfter: document.querySelector("#orbit-word").dataset.boundaryAfter,
    boundaryHidden: document.querySelector("#orbit-boundary").hidden,
    boundaryPosition: document.querySelector("#orbit-boundary").dataset.decimalPosition,
    boundaryText: document.querySelector("#orbit-boundary").textContent,
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
  const baseValueText = `Group ${index + 1} of 332: growing power 3 to exponent ${index}, remainder ${expected.remainder}, three-digit word ${formatWord(expected.word, 1000n)}`;
  const decimalEnd = Math.floor((3 * index + 3) / 166) * 166;
  const cut = decimalEnd > 3 * index ? decimalEnd - 3 * index : 0;
  assert.equal(actual.boundaryHidden, cut === 0);
  if (cut) {
    assert.equal(actual.boundaryAfter, String(cut));
    assert.equal(actual.boundaryPosition, String(decimalEnd));
    assert(actual.valueText.startsWith(baseValueText));
    assert.match(actual.valueText, new RegExp(`decimal digit ${decimalEnd}`));
    assert.match(actual.valueText, /remainder returns to 1/);
    assert.match(actual.boundaryText, /remainder returns to 1/);
  } else {
    assert.equal(actual.valueText, baseValueText);
    assert.equal(actual.boundaryAfter, undefined);
    assert.equal(actual.boundaryPosition, undefined);
    assert.equal(actual.boundaryText, "");
  }
  assert.equal(integer(actual.next), expected.nextRemainder);
}

async function assertOpeningGallery(page) {
  const gallery = page.locator("#specimens");
  const examples = gallery.locator("article.decimal-example");
  assert.equal(await examples.count(), 1);
  const expected = [
    ["997", 6, "243", "729", "731"],
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
  await setDisclosure(page, "#stack-tail-note", true);
  assert.equal(await page.locator("#stack-tail-note .formula").textContent(), "147/1000 + 531441/(997 × 1000) = 678/997 < 1");
  await assertPageFits(page);
  await setDisclosure(page, "#stack-tail-note", false);
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
  await setDisclosure(page, "#decimal-vs-groups", true);
  assert.equal(await card.getByRole("heading", { name: "Halfway, or all the way around?" }).isVisible(), true);
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
      if (index === 55) {
        const note = page.locator("#orbit-boundary");
        assert.equal(await note.isVisible(), true);
        assert.equal(await page.locator("#orbit-word .decimal-word-before").textContent(), "7");
        assert.equal(await page.locator("#orbit-word .decimal-word-after").textContent(), "00");
        assert.match(await note.textContent(), /whole three-digit step ends with remainder 100/);
        await setDisclosure(page, "#orbit-boundary details", true);
        assert.deepEqual(await note.locator(".decimal-step-equation").allTextContents(), [
          "10 × 698 = 997 × 7 + 1", "10 × 1 = 997 × 0 + 10", "10 × 10 = 997 × 0 + 100",
        ]);
        assert.match(await page.locator("#live-status").textContent(), /after 1 digit/);
        await assertPageFits(page);
      }
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
  await setDisclosure(page, "#decimal-vs-groups", false);
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
  for (const id of ["focus-997", "carry", "repeat", "soft-end", "one-digit", "change-radix", "digit-index", "research"]) {
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
  assert.equal(await page.locator("#geometry-app").count(), 0);
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

async function assertRunExplorer(page, interactive = true) {
  await setDisclosure(page, "#run-from-start", true);
  assert.equal(await page.locator("#run-proof").evaluate(el => el.open), false);
  assert.equal(await page.locator("#run-decimals").evaluate(el => el.open), false);
  assert.equal((await page.locator("#run-digit").textContent()).trim(), "27");
  if (interactive) {
    await page.locator("#run-position").focus();
    await page.locator("#run-position").press("ArrowRight");
    assert.equal((await page.locator("#run-digit").textContent()).trim(), "81");
    for (const n of [0, 3, 6, 166, 167, 168]) {
      await page.locator("#run-position").evaluate((el, n) => { el.value = String(n); el.dispatchEvent(new Event("input", { bubbles:true })); }, n);
      const digit = 3n ** BigInt(n);
      assert.equal(await page.locator("#run-digit").getAttribute("data-exact"), String(digit));
      assert.equal(await page.locator("#run-radix").getAttribute("data-exact"), String(997n * digit + 1n));
      assert.equal((await page.locator("#run-exact-digit").textContent()).trim(), String(digit));
      assert.equal((await page.locator("#run-exact-radix").textContent()).trim(), String(997n * digit + 1n));
      if (String(digit).length <= 12) assert.equal((await page.locator("#run-equation").textContent()).trim(), `${997n * digit + 1n} × 1 = 997 × ${digit} + 1`);
      else assert.match(await page.locator("#run-size-note").textContent(), /abbreviated/);
      const P = BigInt(await page.locator("#run-place").inputValue());
      const Q = BigInt(await page.locator("#run-quotient").inputValue());
      assert.equal(P, 997n * Q + 1n);
      await assertPageFits(page);
    }
    assert.equal(await page.locator("#run-next").isDisabled(), true);
    await page.locator("#run-start").click();
    await page.locator("#run-166").click();
    assert.equal(await page.locator("#run-position").inputValue(), "166");
    await setDisclosure(page, "#run-state", true);
    await assertPageFits(page);
    await setDisclosure(page, "#run-state", false);
    await page.locator("#run-start").click();
  } else {
    assert.equal(await page.locator("#run-position").isVisible(), false);
  }
  for (const id of ["run-decimals", "run-proof"]) {
    await setDisclosure(page, "#" + id, true);
    await assertPageFits(page);
    await setDisclosure(page, "#" + id, false);
  }
  await setDisclosure(page, "#run-from-start", false);
}

async function exerciseRunLinks() {
  const context = await browser.newContext({ viewport: { width:320, height:1000 }, reducedMotion:"reduce" });
  await context.addInitScript(() => {
    Object.defineProperty(navigator, "clipboard", { configurable:true, value: { writeText: async text => { window.copiedRunLink = text; } } });
  });
  const page = await context.newPage();
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  for (const [run, n] of [["1",0],["169",168],["0",3],["170",3],["1&run=2",3],["NaN",3]]) {
    await page.goto(shareTestURL + "?group=8&run=" + run + "#change-radix");
    assert.equal(await page.locator("#run-position").inputValue(),String(n));
    assert.equal(await page.locator("#position").inputValue(),"7");
  }
  await page.goto(shareTestURL + "?group=8&run=4#change-radix");
  await page.locator("#run-next").click();
  assert.equal(new URL(page.url()).searchParams.get("group"),"8");
  await page.locator("#next").click();
  assert.equal(new URL(page.url()).searchParams.get("run"),"5");
  await page.evaluate(() => {
    history.pushState(null,"","?group=8&run=167#change-radix");
    dispatchEvent(new PopStateEvent("popstate"));
  });
  assert.equal(await page.locator("#run-position").inputValue(),"166");
  await page.goBack();
  assert.equal(await page.locator("#run-position").inputValue(),"4");
  assert.equal(await page.locator("#position").inputValue(),"8");
  await page.goForward();
  assert.equal(await page.locator("#run-position").inputValue(),"166");
  await page.locator("#share-run").click();
  assert.equal(await page.evaluate(() => window.copiedRunLink),"https://reptends.mikedotexe.com/?run=167#change-radix");
  await page.evaluate(() => { Object.defineProperty(navigator,"clipboard",{ configurable:true,value:{ writeText:async () => { throw new Error("Unavailable"); } } }); });
  await page.locator("#share-run").click();
  assert.equal(await page.locator("#share-run-link").inputValue(),"https://reptends.mikedotexe.com/?run=167#change-radix");
  assert.equal(await page.evaluate(() => document.activeElement.id),"share-run-link");
  await assertPageFits(page);
  assert.deepEqual(errors,[]);
  await context.close();
  console.log(`PASS ${engine} run links: bounds, independent group/run positions, Back/Forward, copied link and selectable fallback.`);
}

try {
  const indexedContext = await browser.newContext({ viewport: { width: 1024, height: 1000 } });
  const indexedPage = await indexedContext.newPage();
  await indexedPage.goto(shareTestURL + "#digit-index");
  await exerciseDigitIndex(indexedPage);
  await indexedPage.goto(shareTestURL + "#change-radix");
  await exerciseProgression(indexedPage);
  console.log(`PASS ${engine} retained progressions: three prefixes, 27 exact states, signed balances, completion, sharing and history.`);
  await exerciseFieldLinks(indexedPage, shareTestURL);
  console.log(`PASS ${engine} field links: independent query parameters, bounds, and same-document Back/Forward restoration.`);
  await exercisePowerDialLinks(indexedPage, shareTestURL);
  console.log(`PASS ${engine} power/grouping links: independent controls, preserved query parameters, bounds, and Back/Forward restoration.`);
  await indexedContext.close();
  console.log(`PASS ${engine} indexed digits: arbitrary bases, huge positions, independent checks, cancellation, sharing and history.`);
  await exerciseRunLinks();
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
      await assertRemainderStory(page);
      await assertFieldLesson(page, true, [320, 768, 1440].includes(width) && colorScheme === "light"
        ? screenshotPath(`${width}-field-strip.png`) : undefined);
      await assertPowerDial(page, true, [320, 1440].includes(width) && colorScheme === "light"
        ? screenshotPath(`${width}-power-and-grouping.png`) : undefined);
      await assertVerificationGuide(page);
      await assertRunExplorer(page);
      for (const example of ["powers", "fibonacci", "counting"]) {
        await page.locator("#hp-" + example).click();
        await assertProgression(page, example, 0);
        if ([320, 1440].includes(width) && colorScheme === "light") {
          await page.locator(".hp-workbench").screenshot({ path: screenshotPath(`${width}-progression-${example}.png`) });
        }
      }
      for (const id of ["notation-examples", "notation-reference"]) {
        await setDisclosure(page, "#" + id, true);
        await assertPageFits(page);
        if ([320, 1440].includes(width) && colorScheme === "light") {
          await page.locator("#" + id).screenshot({ path: screenshotPath(`${width}-${id}.png`) });
        }
        await setDisclosure(page, "#" + id, false);
      }
      await page.locator('[data-di-preset="return"]').click();
      assert.equal(await page.locator("#di-tape").textContent(), "001");
      await setDisclosure(page, "#di-power-bridge", true);
      assert.match(await page.locator("#di-full-power").textContent(), /3\^166/);
      await assertPageFits(page);
      if ([320, 1440].includes(width) && colorScheme === "light") {
        await page.locator("#digit-index").screenshot({ path: screenshotPath(`${width}-digit-index.png`) });
      }
      await page.locator('[data-di-preset="start"]').click();
      if ([320, 1440].includes(width) && colorScheme === "light") {
        await page.locator("#change-radix").screenshot({ path: screenshotPath(`${width}-change-radix.png`) });
      }
      if ([320, 768, 1440].includes(width) && colorScheme === "light") {
        await setDisclosure(page, "#decimal-vs-groups", true);
        await page.locator('[data-boundary-position="55"]').click();
        await setDisclosure(page, "#orbit-boundary details", true);
        await page.locator(".orbit-card").screenshot({ path: screenshotPath(`${width}-decimal-return.png`) });
        await setDisclosure(page, "#decimal-vs-groups", false);
        await page.locator("#reset").click();
      }
      if ([320, 768, 1440].includes(width) && colorScheme === "light") {
        await page.locator("#soft-end").screenshot({ path: screenshotPath(`${width}-soft-end.png`) });
        await page.locator("#one-digit").screenshot({ path: screenshotPath(`${width}-one-digit.png`) });
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
      console.log(`PASS ${engine} ${width}px ${colorScheme}: ${engine === "webkit" ? "local file with offline interaction" : "offline load"}, exact controls, keyboard, run notation, layout bounds, no runtime errors.`);
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
  await assertRemainderStory(fallbackPage, false);
  await assertFieldLesson(fallbackPage, false);
  await assertPowerDial(fallbackPage, false);
  await assertVerificationGuide(fallbackPage, false);
  await assertRunExplorer(fallbackPage, false);
  assert.equal(await fallbackPage.locator("#hp-next").isVisible(), false);
  assert.equal(await fallbackPage.locator("#hp-digit").textContent(), "729");
  await setDisclosure(fallbackPage, "#notation-examples", true);
  assert.equal(await fallbackPage.locator("#notation-examples article").count(),3);
  assert.match(await fallbackPage.locator('[data-example="counting"] .notation-static').textContent(), /⟨998⟩999/);
  await setDisclosure(fallbackPage, "#notation-reference", true);
  assert.match(await fallbackPage.locator("#notation-reference").textContent(), /once for each digit/);
  await assertPageFits(fallbackPage);
  await setDisclosure(fallbackPage, "#notation-examples", false);
  await setDisclosure(fallbackPage, "#notation-reference", false);
  assert.equal(await fallbackPage.locator("#di-form").isVisible(), false);
  assert.match(await fallbackPage.locator("#di-tape").textContent(), /^001003009027081243731193/);
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
  await assertPageFits(motionPage);
  assert.deepEqual(motionErrors, []);
  await motionContext.close();
  console.log(`PASS ${engine} normal motion: visible split movement, finish/restart, cancellation on selection.`);
} finally {
  await browser.close();
  await new Promise(resolve => server.close(resolve));
}
