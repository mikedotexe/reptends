import assert from "node:assert/strict";

// Read decimal digits independently, then group them in threes. This does not
// use the lesson's field predicate, series coefficients, or base-1000 division.
function decimalGroups(denominator) {
  let remainder = 1n;
  let digits = "";
  for (let place = 0; place < 18; place++) {
    remainder *= 10n;
    digits += String(remainder / BigInt(denominator));
    remainder %= BigInt(denominator);
  }
  return digits.match(/.{3}/g);
}

async function assertStage(page, stage) {
  assert.equal(await page.locator("#field-lesson").getAttribute("data-stage"), String(stage));
  for (const step of [1, 2, 3]) {
    assert.equal(await page.locator(`[data-field-go="${step}"]`).getAttribute("aria-pressed"), String(step === stage));
    assert.equal(await page.locator(`[data-field-panel="${step}"]`).isVisible(), step === stage);
  }
  assert.equal(await page.locator("#field-inspector").isVisible(), stage !== 1);
  assert.equal(await page.locator("#field-step-count").textContent(), `Step ${stage} of 3`);
  assert.equal(await page.locator("#field-live-ruler [role='img']").count(), 1);
}

async function assertReading(page, n) {
  assert.equal(await page.locator("#field-denominator").inputValue(), String(n));
  assert.equal(await page.locator("#field-denominator-value").textContent(), String(n));
  assert.equal(await page.locator("#field-reading h4").textContent(), `1/${n}`);
  assert.deepEqual(await page.locator("#field-reading .field-groups span").allTextContents(), decimalGroups(n));
  assert.equal(await page.locator("#field-reading .field-membership").textContent(),
    n >= 969 && n <= 1032 ? "Inside the field" : "Outside the field");
  assert.equal(await page.locator("#field-live-ruler .field-selection-label").textContent(), String(n));
}

async function assertFits(page) {
  const { width, content } = await page.evaluate(() => ({ width: innerWidth, content: document.documentElement.scrollWidth }));
  assert(content <= width + 1, `The field lesson overflows: ${content}px in a ${width}px viewport.`);
}

export async function assertFieldLesson(page, interactive = true, screenshotPath) {
  assert.equal(await page.locator("#nearby-fractions").evaluate(el => el.previousElementSibling.id), "change-radix");
  const proof = page.locator("#field-boundaries");
  assert.equal(await proof.evaluate(el => el.open), false);
  if (interactive) {
    await assertStage(page, 1);
    assert.equal(await page.locator("#field-live-ruler .field-dot").count(), 1);
    assert.match(await page.locator("#field-live-ruler [role='img']").getAttribute("aria-label"), /997.*three below.*1000/);
    await page.locator("#field-next").focus();
    await page.locator("#field-next").press("Enter");
    await assertStage(page, 2);
    await assertReading(page, 997);
    assert.equal(await page.locator("#field-live-ruler .field-dot").count(), 66);
    assert.equal(await page.locator("#field-live-ruler .field-outside").count(), 2);
    assert.match(await page.locator("#field-live-ruler").textContent(), /64 denominators/);
    for (const n of [998, 1003, 969, 968, 1033]) {
      await page.locator(`[data-field-n="${n}"]`).click();
      await assertReading(page, n);
      if (n === 998) assert.match(await page.locator("#field-reading .field-motion").textContent(), /multiplied by 2/);
      if (n === 1003) {
        assert.match(await page.locator("#field-reading .field-motion").textContent(), /alternates.*−3.*Borrowing/);
        assert.match(await page.locator("#field-reading .field-verdict").textContent(), /000, then 997/);
      }
      if (n === 968) assert.match(await page.locator("#field-reading .field-verdict").textContent(), /032 becomes 033/);
      if (n === 1033) assert.match(await page.locator("#field-reading .field-verdict").textContent(), /967 becomes 968/);
    }
    const slider = page.locator("#field-denominator");
    await slider.focus();
    await slider.press("ArrowLeft");
    await assertReading(page, 1032);
    await slider.press("Home");
    await assertReading(page, 968);
    await slider.press("ArrowRight");
    await assertReading(page, 969);
    await slider.press("End");
    await assertReading(page, 1033);
    await page.locator('[data-field-n="997"]').click();
    await page.locator("#field-next").click();
    await assertStage(page, 3);
    await assertReading(page, 997);
    assert.match(await page.locator("#field-live-ruler [role='img']").getAttribute("aria-label"), /square-root.*exactly one unit apart/);
    assert.equal(await page.locator("#field-live-ruler .field-root-measure strong").textContent(), "exactly 1 apart");
    assert.match(await page.locator("#field-live-ruler .field-root-measure").textContent(), /31\.126729.*32\.126729/s);
    await assertFits(page);
    if (screenshotPath) await page.locator("#nearby-fractions").screenshot({ path: screenshotPath });
    await page.locator("#field-next").click();
    await assertStage(page, 1);
    assert.equal(await slider.inputValue(), "997");
  } else {
    for (const step of [1, 2, 3]) {
      assert.equal(await page.locator(`[data-field-panel="${step}"]`).isVisible(), true);
      assert.equal(await page.locator(`[data-field-panel="${step}"] .field-static-ruler [role='img']`).isVisible(), true);
    }
    for (const selector of ["#field-next", "#field-denominator", "[data-field-go='2']", "#field-live-ruler"]) {
      assert.equal(await page.locator(selector).isVisible(), false, `${selector} should be hidden without JavaScript.`);
    }
    assert.deepEqual(await page.locator("#field-reading .field-groups span").allTextContents(), decimalGroups(997));
    assert.match(await page.locator('[data-field-panel="3"]').textContent(), /exactly one unit apart/);
  }
  await proof.locator(":scope > summary").focus();
  await proof.locator(":scope > summary").press("Enter");
  assert.equal(await proof.evaluate(el => el.open), true);
  assert.match(await proof.textContent(), /\(1000 − n\)² = n/);
  assert.match(await proof.textContent(), /y = x \+ 1/);
  assert.match(await proof.textContent(), /968\.873270.*1032\.126729/s);
  await assertFits(page);
  await proof.locator(":scope > summary").press("Enter");
  assert.equal(await proof.evaluate(el => el.open), false);
}

export async function exerciseFieldLinks(page, siteURL) {
  await page.goto(`${siteURL}?group=8&hp=fibonacci&field_n=998&field_step=2#nearby-fractions`);
  await assertStage(page, 2);
  await assertReading(page, 998);
  await page.locator('[data-field-n="1003"]').click();
  await page.locator('[data-field-go="3"]').click();
  await assertStage(page, 3);
  const selected = new URL(page.url());
  assert.equal(selected.searchParams.get("field_n"), "1003");
  assert.equal(selected.searchParams.get("field_step"), "3");
  assert.equal(selected.searchParams.get("group"), "8");
  assert.equal(selected.searchParams.get("hp"), "fibonacci");
  assert.equal(selected.hash, "#nearby-fractions");

  // Create a second same-document history entry. Each lesson control replaces
  // its current entry; native Back/Forward must restore the prior selection.
  const next = new URL(selected);
  next.searchParams.set("group", "9");
  await page.evaluate(url => history.pushState(null, "", url), next.href);
  await page.locator('[data-field-go="2"]').click();
  await page.locator('[data-field-n="969"]').click();
  await page.goBack();
  await page.waitForFunction(() => document.querySelector("#field-lesson").dataset.stage === "3"
    && document.querySelector("#field-denominator").value === "1003");
  await assertReading(page, 1003);
  assert.equal(await page.locator("#position").inputValue(), "7");
  await page.goForward();
  await page.waitForFunction(() => document.querySelector("#field-lesson").dataset.stage === "2"
    && document.querySelector("#field-denominator").value === "969");
  await assertReading(page, 969);
  assert.equal(await page.locator("#position").inputValue(), "8");

  for (const [query, stage, n] of [
    ["field_n=1003", 2, 1003],
    ["field_n=967&field_step=3", 3, 997],
    ["field_n=1034&field_step=2", 2, 997],
    ["field_n=1003&field_step=4", 1, 997],
  ]) {
    await page.goto(`${siteURL}?${query}#nearby-fractions`);
    await assertStage(page, stage);
    assert.equal(await page.locator("#field-denominator").inputValue(), String(n));
  }
}
