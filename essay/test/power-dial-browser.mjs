import assert from "node:assert/strict";

// Walk ordinary decimal division one digit at a time. These expectations do
// not import the power dial's model, grouped division, or geometric-series code.
function decimalDigits(denominator, places) {
  let remainder = 1n;
  let digits = "";
  for (let place = 0; place < places; place++) {
    remainder *= 10n;
    digits += String(remainder / BigInt(denominator));
    remainder %= BigInt(denominator);
  }
  return digits;
}

function reading(denominator, width) {
  const base = 10n ** BigInt(width);
  const n = BigInt(denominator);
  const quotient = base / n;
  const remainder = base % n;
  const digits = decimalDigits(n, width * 16);
  const groups = Array.from({ length: 16 }, (_, i) => digits.slice(i * width, (i + 1) * width));
  let expected = quotient;
  let cleanCount = 0;
  while (cleanCount < groups.length && BigInt(groups[cleanCount]) === expected) {
    cleanCount++;
    expected *= remainder;
  }
  assert(cleanCount < groups.length, "The independent decimal walk must reach the first changed group.");
  return { quotient, remainder, groups, cleanCount, expected, actual: groups[cleanCount] };
}

function fieldCount(base) {
  // The membership inequality is exact over integers, including the strict
  // boundary. Count candidates without using the lesson's edge formula.
  let count = 0;
  const reach = Math.ceil(Math.sqrt(base)) + 2;
  for (let n = base - reach; n <= base + reach; n++) {
    const gap = BigInt(base - n);
    if (gap * gap < BigInt(n)) count++;
  }
  return count;
}

const cleanCounts = new Map([[2, 4], [3, 6], [4, 8], [5, 10], [6, 12]]);
const fieldCounts = new Map([[2, 20], [3, 64], [4, 200], [5, 632], [6, 2000]]);
const fixedReadings = new Map([
  [3, [1n, 3n, 6, 729n, "731"]],
  [4, [10n, 30n, 2, 9000n, "9027"]],
  [5, [100n, 300n, 1, 30000n, "30090"]],
  [6, [1003n, 9n, 3, 731187n, "731193"]],
]);

async function text(page, selector) {
  return (await page.locator(selector).textContent()).trim();
}

async function assertFamily(page, width, interactive = true) {
  const base = 10 ** width;
  const expected = reading(base - 3, width);
  assert.equal(expected.cleanCount, cleanCounts.get(width));
  assert.equal(await text(page, "#power-fraction"), `1/${base - 3}`);
  if (interactive) assert.equal(await page.locator("#power-width").inputValue(), String(width));
  assert.deepEqual(await page.locator(".power-clean-groups span").allTextContents(), expected.groups.slice(0, expected.cleanCount));
  assert.equal(await text(page, "#power-count"), String(expected.cleanCount));
  assert.equal(await text(page, "#power-next-expected"), String(expected.expected));
  assert.equal(await text(page, "#power-next-actual"), expected.actual);
  const count = fieldCount(base);
  assert.equal(count, fieldCounts.get(width));
  assert.equal(await text(page, "#power-field-count"), String(count));
  assert.equal(await text(page, "#power-root-width"), "1");
  const lower = Number.parseFloat((await text(page, "#power-root-lower")).replaceAll(",", ""));
  const upper = Number.parseFloat((await text(page, "#power-root-upper")).replaceAll(",", ""));
  assert(Math.abs(lower - (Math.sqrt(4 * base + 1) - 1) / 2) < 1e-4, `Wrong lower square-root endpoint for 10^${width}.`);
  assert(Math.abs(upper - lower - 1) < 1e-4, `The square-root strip is not one unit wide for 10^${width}.`);
  assert.equal(await page.locator("#power-result").isVisible(), true);
  assert.equal(await page.locator("#group-result").isVisible(), true);
}

async function assertGrouping(page, width, interactive = true) {
  const expected = reading(997, width);
  assert.deepEqual([expected.quotient, expected.remainder, expected.cleanCount, expected.expected, expected.actual], fixedReadings.get(width));
  if (interactive) assert.equal(await page.locator("#group-width").inputValue(), String(width));
  assert.equal(await text(page, "#group-quotient"), String(expected.quotient));
  assert.equal(await text(page, "#group-remainder"), String(expected.remainder));
  assert.equal(await text(page, "#group-clean-count"), String(expected.cleanCount));
  assert.equal(await text(page, "#group-next-expected"), String(expected.expected));
  assert.equal(await text(page, "#group-next-actual"), String(BigInt(expected.actual)));
  const equation = (await text(page, "#group-equation")).replaceAll(",", "").replace(/\s/g, "");
  assert.equal(equation, `${10 ** width}=997×${expected.quotient}+${expected.remainder}`);
  const tape = await page.locator("#group-tape .group-digit-word").allTextContents();
  assert.equal(tape.length, 60 / width);
  assert(tape.every(word => word.length === width), "Each tape word should keep its leading zeroes.");
  assert.equal(tape.join(""), decimalDigits(997, 60), "Regrouping must preserve the same first 60 decimal digits.");
  const changes = await page.locator("#group-tape .group-digit-word").evaluateAll(words => words.flatMap((word, i) => word.hasAttribute("data-change") ? [i] : []));
  assert.deepEqual(changes, [expected.cleanCount], "Only the first changed group should receive the change marker.");
}

async function assertFits(page) {
  const { width, content } = await page.evaluate(() => ({ width: innerWidth, content: document.documentElement.scrollWidth }));
  assert(content <= width + 1, `The power and grouping lesson overflows: ${content}px in a ${width}px viewport.`);
}

export async function assertPowerDial(page, interactive = true, screenshotPath) {
  assert.equal(await page.locator("#power-and-grouping").evaluate(el => el.previousElementSibling.id), "nearby-fractions");
  assert.equal(await page.locator("#power-and-grouping [role='tab']").count(), 0, "The two experiments should be visible together.");
  await assertFamily(page, 3, interactive);
  await assertGrouping(page, 3, interactive);
  if (!interactive) {
    assert.equal(await page.locator("#power-answer").isVisible(), true, "The static lesson should include its answer.");
    for (const selector of ["#power-width", "#group-width", "#power-reveal", "[data-power-width='4']", "[data-group-width='4']"]) {
      assert.equal(await page.locator(selector).isVisible(), false, `${selector} should be hidden without JavaScript.`);
    }
    await assertFits(page);
    return;
  }

  const originalURL = page.url();
  assert.equal(await page.locator("#power-answer").isVisible(), false);
  const barWidths = [];
  for (const width of [2, 3, 4, 5, 6]) {
    await page.locator(`[data-power-width="${width}"]`).click();
    await assertFamily(page, width);
    await assertGrouping(page, 3);
    assert.equal(await page.locator("#power-answer").isVisible(), false);
    const bar = await page.locator("#power-number-bar").evaluate(el => el.style.width);
    assert.match(bar, /%$/, "The ordinary-width comparison should use a percentage width.");
    barWidths.push(Number.parseFloat(bar));
    await assertFits(page);
  }
  assert(barWidths.every((width, i) => width > 0 && (i === 0 || width > barWidths[i - 1])), "The ordinary number strip should grow as the power increases.");

  const powerSlider = page.locator("#power-width");
  await powerSlider.focus();
  for (const [key, width] of [["Home", 2], ["End", 6], ["ArrowLeft", 5], ["ArrowRight", 6]]) {
    await powerSlider.press(key);
    await assertFamily(page, width);
  }
  await page.locator('[data-power-width="3"]').click();
  await page.locator("#power-reveal").focus();
  await page.locator("#power-reveal").press("Enter");
  assert.equal(await page.locator("#power-answer").isVisible(), true);
  await page.locator("#power-reveal").click();
  assert.equal(await page.locator("#power-answer").isVisible(), false);
  await page.locator("#power-reveal").click();

  for (const width of [3, 4, 5, 6]) {
    await page.locator(`[data-group-width="${width}"]`).click();
    await assertGrouping(page, width);
    await assertFamily(page, 3);
    assert.equal(await page.locator("#power-answer").isVisible(), true, "Regrouping 997 should preserve the other experiment's revealed answer.");
    await assertFits(page);
  }
  const groupSlider = page.locator("#group-width");
  await groupSlider.focus();
  for (const [key, width] of [["Home", 3], ["End", 6], ["ArrowLeft", 5], ["ArrowRight", 6]]) {
    await groupSlider.press(key);
    await assertGrouping(page, width);
    assert.equal(await page.locator("#power-answer").isVisible(), true);
  }
  await page.locator('[data-power-width="4"]').click();
  await assertFamily(page, 4);
  await assertGrouping(page, 6);
  assert.equal(await page.locator("#power-answer").isVisible(), false, "A new denominator should invite a fresh prediction.");
  await page.locator('[data-power-width="3"]').click();
  await page.locator('[data-group-width="3"]').click();
  await page.locator("#power-reveal").click();
  if (screenshotPath) await page.locator("#power-and-grouping").screenshot({ path: screenshotPath });
  await page.locator("#power-reveal").click();
  await assertFamily(page, 3);
  await assertGrouping(page, 3);
  await assertFits(page);
  if (new URL(originalURL).protocol === "file:") assert.equal(page.url(), originalURL, "Offline lesson controls should not mutate file URLs.");
}

export async function exercisePowerDialLinks(page, siteURL) {
  await page.goto(`${siteURL}?group=8&hp=fibonacci&field_n=998&field_step=2&run=4&power_width=4&power_reveal=1&group_width=5#power-and-grouping`);
  await assertFamily(page, 4);
  await assertGrouping(page, 5);
  assert.equal(await page.locator("#power-answer").isVisible(), true);
  await page.locator('[data-group-width="6"]').click();
  assert.equal(await page.locator("#power-answer").isVisible(), true);
  await page.locator('[data-power-width="5"]').click();
  assert.equal(await page.locator("#power-answer").isVisible(), false);
  await page.locator("#power-reveal").click();
  const selected = new URL(page.url());
  for (const [name, value] of Object.entries({ group: "8", hp: "fibonacci", field_n: "998", field_step: "2", run: "4", power_width: "5", power_reveal: "1", group_width: "6" })) {
    assert.equal(selected.searchParams.get(name), value, `The power lesson should preserve ${name}.`);
  }
  assert.equal(selected.hash, "#power-and-grouping");

  // The controls replace their entry. Native history restores all three new
  // settings together, alongside the existing remainder/field explorers.
  const next = new URL(selected);
  next.searchParams.set("group", "9");
  await page.evaluate(url => history.pushState(null, "", url), next.href);
  await page.locator('[data-power-width="2"]').click();
  await page.locator('[data-group-width="4"]').click();
  await page.goBack();
  await page.waitForFunction(() => document.querySelector("#power-width").value === "5" && document.querySelector("#group-width").value === "6" && !document.querySelector("#power-answer").hidden);
  await assertFamily(page, 5);
  await assertGrouping(page, 6);
  assert.equal(await page.locator("#position").inputValue(), "7");
  assert.equal(await page.locator("#field-denominator").inputValue(), "998");
  await page.goForward();
  await page.waitForFunction(() => document.querySelector("#power-width").value === "2" && document.querySelector("#group-width").value === "4" && document.querySelector("#power-answer").hidden);
  await assertFamily(page, 2);
  await assertGrouping(page, 4);
  assert.equal(await page.locator("#position").inputValue(), "8");

  for (const query of [
    "power_width=1&group_width=2",
    "power_width=7&group_width=7",
    "power_width=3.5&group_width=4.5",
    "power_width=invalid&group_width=invalid&power_reveal=invalid",
  ]) {
    await page.goto(`${siteURL}?${query}#power-and-grouping`);
    await assertFamily(page, 3);
    await assertGrouping(page, 3);
    assert.equal(await page.locator("#power-answer").isVisible(), false);
  }
}
