import assert from "node:assert/strict";

export async function assertProgression(page, example, step) {
  const d = example === "powers" ? 729n * 3n ** BigInt(step) : 998n + BigInt(step);
  const D = example === "powers" ? 997n : 998001n;
  const R = example === "powers" ? 997n * 3n ** BigInt(step) + 1n
    : step === 0 ? 999n : 999n * d + 1n;
  const r = example === "powers" ? 729n : 999n;
  assert.equal((await page.locator("#hp-digit").textContent()).trim(), String(d));
  assert.equal((await page.locator("#hp-radix").textContent()).trim(), String(R));
  assert.match(await page.locator("#hp-position-note").textContent(), new RegExp(`position ${step + (example === "powers" ? 7 : 999)}\\b`));
  const P = BigInt(await page.locator("#hp-place").inputValue());
  const Q = BigInt(await page.locator("#hp-quotient").inputValue());
  assert.equal(D * Q + r, P);
  assert.equal(await page.locator("#hp-" + example).getAttribute("aria-pressed"), "true");
  assert.equal(await page.locator("#hp-fixed-first").textContent(), example === "powers" ? "731" : "999");
  assert.equal(await page.locator("#hp-changed-first").textContent(), example === "powers" ? "729" : "998");
  const dimensions = await page.evaluate(() => [innerWidth, document.documentElement.scrollWidth]);
  assert(dimensions[1] <= dimensions[0] + 1, `Progression overflows ${dimensions[0]}px viewport.`);
}

export async function exerciseProgression(page) {
  const url = new URL(page.url());
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  for (const example of ["powers", "counting"]) {
    await page.locator("#hp-" + example).click();
    for (let step = 0; step < 8; step++) {
      await assertProgression(page, example, step);
      if (step < 7) await page.locator("#hp-next").click();
    }
    assert.equal(await page.locator("#hp-next").isDisabled(), true);
    await page.locator("#hp-previous").click();
    await assertProgression(page, example, 6);
  }
  await page.locator("#hp-weights > summary").click();
  await page.locator("#hp-exact > summary").click();
  await assertProgression(page, "counting", 6);
  assert.equal(await page.locator("#hp-place").isVisible(), true);
  await page.locator("#hp-weights > summary").click();
  for (const [query, example, step] of [
    ["?group=8&run=167&hp=counting&hp_step=3", "counting", 2],
    ["?hp=powers&hp_step=8", "powers", 7],
    ["?hp=unknown&hp_step=NaN", "powers", 0],
    ["?hp=powers&hp=counting&hp_step=1", "powers", 0],
    ["?hp=counting&hp_step=9", "counting", 0],
    ["?hp=counting&hp_step=2&hp_step=3", "counting", 0],
  ]) {
    await page.goto(url.origin + url.pathname + query + "#change-radix");
    await assertProgression(page, example, step);
  }
  await page.goto(url.origin + url.pathname + "?group=8&run=167&hp=counting&hp_step=3#change-radix");
  await page.locator("#hp-next").click();
  assert.equal(new URL(page.url()).searchParams.get("group"), "8");
  assert.equal(new URL(page.url()).searchParams.get("run"), "167");
  assert.equal(new URL(page.url()).searchParams.get("hp_step"), "4");
  await page.evaluate(() => {
    const next = new URL(location.href);
    next.searchParams.set("hp", "powers");
    next.searchParams.set("hp_step", "2");
    history.pushState(null, "", next);
    dispatchEvent(new PopStateEvent("popstate"));
  });
  await assertProgression(page, "powers", 1);
  await page.goBack();
  await assertProgression(page, "counting", 3);
  await page.goForward();
  await assertProgression(page, "powers", 1);
  await page.evaluate(() => Object.defineProperty(navigator, "clipboard", {
    configurable: true, value: { writeText: async value => { window.__hpCopied = value; } },
  }));
  await page.locator("#hp-share").click();
  const shared = new URL(await page.evaluate(() => window.__hpCopied));
  assert.equal(shared.hostname, "reptends.mikedotexe.com");
  assert.equal(shared.searchParams.get("hp"), "powers");
  assert.equal(shared.searchParams.get("hp_step"), "2");
  assert.equal(shared.hash, "#change-radix");
  await page.evaluate(() => Object.defineProperty(navigator, "clipboard", {
    configurable: true, value: { writeText: async () => { throw new Error("Unavailable"); } },
  }));
  await page.locator("#hp-share").click();
  assert.equal(await page.locator("#hp-share-link").inputValue(), shared.href);
  assert.equal(await page.evaluate(() => document.activeElement.id), "hp-share-link");
  assert.deepEqual(errors, []);
}
