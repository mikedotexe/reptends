import assert from "node:assert/strict";

export async function assertRemainderStory(page, interactive = true) {
  assert.equal(await page.locator("#one-digit .decimal-tiles span").count(), 6);
  assert.equal(await page.locator("#one-digit .block-tile").textContent(), "142857");
  assert.equal(await page.locator("#one-digit .block-division .equation").textContent(), "1,000,000 × 1 = 7 × 142857 + 1");
  assert.equal(await page.locator("#one-digit").evaluate(el => el.previousElementSibling.id), "soft-end");
  assert.equal(await page.locator("#one-digit").evaluate(el => el.nextElementSibling.id), "change-radix");
  if (interactive) {
    for (const [index, left, right] of [[0, "001", "998"], [6, "731", "268"], [82, "332", "667"]]) {
      const button = page.locator(`[data-mirror-pair="${index}"]`);
      await button.focus();
      await button.press("Enter");
      assert.equal(await page.locator("#mirror-first-word").textContent(), left);
      assert.equal(await page.locator("#mirror-second-word").textContent(), right);
      assert.equal(await page.locator("#mirror-first-position").textContent(), `Group ${index + 1}`);
      assert.equal(await page.locator("#mirror-second-position").textContent(), `Group ${index + 84}`);
      assert.equal(await page.locator("#mirror-sum").textContent(), `${left} + ${right} = 999`);
      assert.equal(BigInt(await page.locator("#mirror-first-remainder").textContent()) + BigInt(await page.locator("#mirror-second-remainder").textContent()), 997n);
    }
    const slider = page.locator("#mirror-position");
    await slider.focus();
    await slider.press("Home");
    await slider.press("ArrowRight");
    assert.equal(await slider.inputValue(), "1");
    assert.equal(await page.locator("#mirror-sum").textContent(), "003 + 996 = 999");
    await page.locator('[data-mirror-pair="0"]').click();
    for (const [button, index, expected] of [["midpoint-jump", "82", /First half complete.*996/], ["group-return-jump", "165", /Full grouped loop complete.*returns to 1/]]) {
      await page.locator("#" + button).click();
      assert.equal(await page.locator("#position").inputValue(), index);
      assert.equal(await page.locator("#group-boundary").isVisible(), true);
      assert.match(await page.locator("#group-boundary").textContent(), expected);
    }
    await page.locator("#reset").click();
    assert.equal(await page.locator("#group-boundary").isVisible(), false);
  } else {
    assert.equal(await page.locator("#mirror-sum").textContent(), "001 + 998 = 999");
    assert.equal(await page.locator("#mirror-position").isVisible(), false);
    assert.equal(await page.locator("#midpoint-jump").isVisible(), false);
  }
}
