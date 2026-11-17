import assert from "node:assert/strict";

function referenceDigits(numerator, denominator, radix, start, count) {
  let remainder = numerator % denominator;
  const values = [];
  for (let position = 1; position < start + count; position++) {
    const scaled = radix * remainder;
    if (position >= start) values.push(scaled / denominator);
    remainder = scaled % denominator;
  }
  const alphabet = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
  return values.map(value => radix <= 36n ? alphabet[Number(value)]
    : radix === 1000n ? String(value).padStart(3, "0") : `[${value}]`).join(radix <= 36n ? "" : " ");
}

/** Shared local-browser checks. The caller supplies an already-loaded page. */
export async function exerciseDigitIndex(page) {
  const originalURL = page.url();
  await page.locator("#di-tape").waitFor();
  const tape = () => page.locator("#di-tape").textContent();
  const preset = async name => page.locator(`[data-di-preset="${name}"]`).click();
  async function enter({ a = "1", d = "997", b = "10", from = "1", to = "" }) {
    for (const [id, value] of Object.entries({
      "di-numerator": a, "di-denominator": d, "di-radix": b, "di-from": from, "di-to": to,
    })) await page.locator("#" + id).fill(value);
    await page.locator("#di-form button[type=submit]").click();
  }
  async function waitForCheck() {
    await page.waitForFunction(() => document.getElementById("di-check-status").textContent.startsWith("Confirmed."));
  }
  async function allowCancelledJobToResume() {
    // A stopped check is suspended on a zero-delay yield. Let that callback
    // resume so a stale completion would have an opportunity to break the UI.
    await page.evaluate(() => new Promise(resolve => setTimeout(resolve, 25)));
  }

  try {
    await preset("start");
    assert.equal(await tape(), referenceDigits(1n, 997n, 10n, 1, 60));
    assert.equal(await page.locator("#di-error").isVisible(), false);
    assert.equal(await page.locator("#di-check-start").isEnabled(), true);
    await page.locator("#di-check-start").click();
    await waitForCheck();
    assert.match(await page.locator("#di-check-status").textContent(), /entering remainder and all 60 requested digits/);

    await preset("huge");
    assert.equal(await tape(), "6");
    assert.match(await page.locator("#di-result-title").textContent(), /10\^100/);
    assert.equal(await page.locator("#di-check-start").isDisabled(), true);
    assert.match(await page.locator("#di-check-help").textContent(), /limits a sequential check to position 100000/);

    await preset("far");
    assert.equal(await tape(), "8");
    assert.equal(await page.locator("#di-check-start").isDisabled(), true);

    await preset("return");
    assert.equal(await tape(), "001");
    assert.match(await page.locator("#di-result-base").textContent(), /Base 1000/);
    assert.match(await page.locator("#di-result-note").textContent(), /not an individual decimal-place number/);
    assert.equal(await page.locator("#di-power-bridge").isVisible(), true);
    await page.locator("#di-power-bridge").evaluate(element => { element.open = true; });
    assert.equal(await page.locator("#di-full-power").textContent(), `3^166 = ${3n ** 166n}`);
    assert.equal(await page.locator("#di-power-quotient").textContent(), String(3n ** 166n / 997n));
    assert.equal(await page.locator("#di-power-carry").textContent(), String(3n ** 167n / 997n));
    assert.match(await page.locator("#di-power-equation").textContent(), / = 1$/);
    await page.locator("#di-check-start").click();
    await waitForCheck();
    await page.locator("#di-power-bridge").evaluate(element => { element.open = false; });

    await preset("improper");
    assert.equal(await tape(), "142857".repeat(5));
    assert.match(await page.locator("#di-result-note").textContent(), /whole-number part is 3/);
    assert.equal(await page.locator("#di-power-bridge").isVisible(), false);

    await enter({ a: "3", d: "7", b: "16", from: "1", to: "12" });
    assert.equal(await tape(), "6DB".repeat(4));
    assert.match(await page.locator("#di-result-note").textContent(), /A–Z/);
    await enter({ a: "0", d: "997", from: "5", to: "8" });
    assert.equal(await tape(), "0000");
    assert.match(await page.locator("#di-result-note").textContent(), /whole number/);
    await enter({ d: "8", from: "1", to: "8" });
    assert.equal(await tape(), "12500000");
    assert.match(await page.locator("#di-result-note").textContent(), /remaining digits.*zero/);
    await enter({ d: "8", from: "10", to: "12" });
    assert.equal(await tape(), "000");
    assert.match(await page.locator("#di-result-note").textContent(), /already terminated/);
    await enter({ d: "7", from: "4", to: "9" });
    assert.equal(await tape(), "857142");

    const lastValid = await tape();
    await page.locator("#di-denominator").fill("0");
    assert.equal(await page.locator("#di-check-start").isDisabled(), true);
    assert.match(await page.locator("#di-check-status").textContent(), /Inputs changed/);
    await page.locator("#di-form button[type=submit]").click();
    assert.equal(await page.locator("#di-error").isVisible(), true);
    assert.match(await page.locator("#di-check-status").textContent(), /last valid search/);
    assert.equal(await tape(), lastValid);
    assert.equal(await page.locator("#di-check-start").isDisabled(), true);
    await enter({ d: "7", from: "1", to: "1001" });
    assert.match(await page.locator("#di-error").textContent(), /at most 1000/);
    await enter({ d: "7", from: "0^999999999999999999999", to: "" });
    assert.match(await page.locator("#di-error").textContent(), /exponent/);

    // Test cancellation at a known asynchronous boundary, independent of CPU speed.
    await enter({ d: "7", from: "100000", to: "" });
    const stopped = await page.evaluate(() => {
      document.getElementById("di-check-start").click();
      const active = !document.getElementById("di-check-stop").hidden;
      document.getElementById("di-check-stop").click();
      return { active, status: document.getElementById("di-check-status").textContent };
    });
    assert.equal(stopped.active, true);
    assert.match(stopped.status, /^Stopped after /);
    await allowCancelledJobToResume();
    assert.equal(await page.locator("#di-check-status").textContent(), stopped.status);
    assert.equal(await page.locator("#di-check-stop").isVisible(), false);

    await page.evaluate(() => {
      document.getElementById("di-check-start").click();
      const input = document.getElementById("di-numerator");
      input.value = "2";
      input.dispatchEvent(new Event("input", { bubbles: true }));
    });
    await allowCancelledJobToResume();
    assert.match(await page.locator("#di-check-status").textContent(), /Inputs changed/);
    assert.equal(await page.locator("#di-check-start").isDisabled(), true);
    // Start a fresh small check before the cancelled long job can finish.
    await enter({ d: "7", from: "100000", to: "" });
    await page.evaluate(() => {
      document.getElementById("di-check-start").click();
      document.querySelector('[data-di-preset="start"]').click();
      document.getElementById("di-check-start").click();
    });
    await waitForCheck();
    await allowCancelledJobToResume();
    assert.match(await page.locator("#di-check-status").textContent(), /all 60 requested digits/);
    assert.equal(await tape(), referenceDigits(1n, 997n, 10n, 1, 60));

    await page.evaluate(() => {
      window.__digitIndexClipboardDescriptor = Object.getOwnPropertyDescriptor(navigator, "clipboard");
      Object.defineProperty(navigator, "clipboard", {
        configurable: true,
        value: { writeText: async () => { throw new Error("Clipboard denied for fallback test"); } },
      });
    });
    try {
      await page.locator("#di-copy").click();
      await page.locator("#di-copy-field-label").waitFor({ state: "visible" });
      assert.equal(await page.locator("#di-copy-field").inputValue(), await tape());
      assert.deepEqual(await page.locator("#di-copy-field").evaluate(field => ({
        selected: field.selectionStart === 0 && field.selectionEnd === field.value.length,
        focused: document.activeElement === field,
      })), { selected: true, focused: true });
      await page.locator("#di-share").click();
      await page.waitForFunction(() => document.getElementById("di-copy-field").value.startsWith("https://reptends.mikedotexe.com/"));
      const link = new URL(await page.locator("#di-copy-field").inputValue());
      assert.equal(link.searchParams.get("di_d"), "997");
      assert.equal(link.searchParams.get("di_from"), "1");
      assert.equal(link.searchParams.get("di_to"), "60");
      assert.equal(link.hash, "#digit-index");
    } finally {
      await page.evaluate(() => {
        if (window.__digitIndexClipboardDescriptor) Object.defineProperty(navigator, "clipboard", window.__digitIndexClipboardDescriptor);
        else delete navigator.clipboard;
        delete window.__digitIndexClipboardDescriptor;
      });
    }

    if (/^https?:/.test(originalURL)) {
      const linked = new URL(originalURL);
      linked.search = "?group=8&run=167&sentinel=keep";
      linked.hash = "digit-index";
      await page.goto(linked.href);
      assert.equal(await tape(), referenceDigits(1n, 997n, 10n, 1, 60));
      await preset("far");
      assert.equal(await tape(), "8");
      for (const [key, value] of [["group", "8"], ["run", "167"], ["sentinel", "keep"]]) {
        assert.equal(new URL(page.url()).searchParams.get(key), value);
      }
      await preset("return");
      assert.equal(await tape(), "001");
      await page.goBack();
      await page.waitForFunction(() => document.getElementById("di-tape").textContent === "8");
      assert.equal(await page.locator("#di-from").inputValue(), "1000000000");
      await page.goBack();
      await page.waitForFunction(() => document.getElementById("di-from").value === "1");
      assert.equal(await tape(), referenceDigits(1n, 997n, 10n, 1, 60));
      await page.goForward();
      await page.waitForFunction(() => document.getElementById("di-tape").textContent === "8");
      assert.equal(new URL(page.url()).searchParams.get("sentinel"), "keep");
      // Navigation during a running check aborts it and restores the linked result.
      await enter({ d: "7", from: "100000", to: "" });
      await page.evaluate(() => document.getElementById("di-check-start").click());
      await page.goBack();
      await page.waitForFunction(() => document.getElementById("di-tape").textContent === "8");
      await allowCancelledJobToResume();
      assert.equal(await page.locator("#di-check-status").textContent(), "");
      assert.equal(await page.locator("#di-check-stop").isVisible(), false);
    }
  } finally {
    // Existing essay checks begin from their own saved URL and control state.
    await page.goto(originalURL);
  }
}
