import assert from "node:assert/strict";

export async function assertProgression(page, example, step) {
  const fib = [[55n,100n,8955n], [89n,99n,5534n], [144n,258n,2316n],
    [233n,996n,269n], [377n,13874n,183n], [610n,32997n,61n],
    [987n,160170n,57n], [1597n,277346n,19n], [2584n,1346265n,19n]];
  const [d, R, r] = example === "fibonacci" ? fib[step + 1]
    : example === "powers" ? (step === -1 ? [243n,1000n,729n]
      : [729n * 3n ** BigInt(step), 997n * 3n ** BigInt(step) + 1n,729n])
    : step === -1 ? [997n,1000n,997003n]
    : [998n + BigInt(step),step === 0 ? 999n : 999n * (998n + BigInt(step)) + 1n,999n];
  const D = example === "powers" ? 997n : example === "fibonacci" ? 9899n : 998001n;
  const first = example === "powers" ? 7 : example === "fibonacci" ? 12 : 999;
  assert.equal((await page.locator("#hp-digit").textContent()).trim(), String(d));
  assert.equal((await page.locator("#hp-radix").textContent()).trim(), String(R));
  assert.match(await page.locator("#hp-position-note").textContent(), new RegExp(`position ${step + first}\\b`));
  const P = BigInt(await page.locator("#hp-place").inputValue());
  const Q = BigInt(await page.locator("#hp-quotient").inputValue());
  assert.equal(D * Q + r, P);
  assert.equal(await page.locator("#hp-" + example).getAttribute("aria-pressed"), "true");
  assert.equal(await page.locator("#hp-fixed-first").textContent(), example === "powers" ? "731" : example === "fibonacci" ? "90" : "999");
  assert.equal(await page.locator("#hp-changed-first").textContent(), example === "powers" ? "729" : example === "fibonacci" ? "89" : "998");
  assert.match(await page.locator("#hp-decision").textContent(), step === -1 ? /Keep/ : /Change/);
  if (example === "fibonacci" && step === 1) {
    assert.match(await page.locator("#hp-balance").textContent(), /−877590|-877590/);
    assert.match(await page.locator("#hp-reason").textContent(), /negative|below zero/);
  }
  assert.equal(await page.locator("#hp-prefix-base").textContent(),example === "fibonacci" ? "100" : "1000");
  assert.match(await page.locator("#hp-prefix").textContent(),/^⟨.*⟩$/);
  if(step === -1) assert.equal(await page.locator("#hp-prefix-run").getAttribute("aria-current"),"step");
  assert.equal(await page.locator("#hp-window-note").isVisible(),step >= 2);
  if(step>=0) assert.equal(await page.locator('#hp-inscription [aria-current="step"] > span').textContent(),`⟨${d}⟩`);
  assert.match(await page.locator("#hp-inscription").getAttribute("aria-label"),/continue the generator and balance rule/);
  const dimensions = await page.evaluate(() => [innerWidth, document.documentElement.scrollWidth]);
  assert(dimensions[1] <= dimensions[0] + 1, `Progression overflows ${dimensions[0]}px viewport.`);
}

export async function exerciseProgression(page) {
  const url = new URL(page.url());
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  for (const example of ["powers", "fibonacci", "counting"]) {
    await page.locator("#hp-" + example).click();
    await page.locator("#hp-previous").click();
    await assertProgression(page, example, -1);
    assert.equal(await page.locator("#hp-previous").isDisabled(), true);
    await page.locator("#hp-next").click();
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
    ["?hp=fibonacci&hp_step=2", "fibonacci", 1],
    ["?hp=fibonacci&hp_step=0", "fibonacci", -1],
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
  await page.locator("#hp-finish > summary").click();
  assert.match(await page.locator("#hp-finish").textContent(), /0\.125/);
  assert.match(await page.locator("#hp-finish").textContent(), /zero/);
  await page.locator("#notation-examples > summary").click();
  assert.equal(await page.locator("#notation-examples article").count(),3);
  await page.locator("#notation-reference > summary").click();
  assert.match(await page.locator("#notation-reference").textContent(),/typography and browser are not formally verified/);
  const certificate=JSON.parse(await page.locator("script#reptends-notation").textContent());
  assert.equal(certificate.examples[2].runs[0].digits.length,998);
  const layout=await page.evaluate(()=>[innerWidth,document.documentElement.scrollWidth]);
  assert(layout[1]<=layout[0]+1);
  assert.deepEqual(errors, []);
}
