import assert from "node:assert/strict";
import test from "node:test";
import { decimalReturn997 } from "../src/decimal-return.ts";
import { recurrenceTrace } from "../src/math/lifts.ts";

test("all six decimal returns match independent digitwise division across two grouped cycles", () => {
  const trace = recurrenceTrace({ base: 1000n, coefficients: [3n] }, 332);
  const expectedReturns: number[] = [];
  const observedReturns: number[] = [];
  let remainder = 1n;
  for (const row of trace.rows) {
    const steps = [];
    let digits = "";
    for (let offset = 1; offset <= 3; offset++) {
      const scaled = remainder * 10n;
      const next = scaled % 997n;
      const digit = scaled / 997n;
      steps.push({ position: 3 * row.index + offset, digit, remainder, nextRemainder: next });
      digits += String(digit);
      remainder = next;
      if (remainder === 1n) expectedReturns.push(3 * row.index + offset);
    }
    assert.equal(digits, row.word.toString().padStart(3, "0"));
    const boundary = decimalReturn997(row);
    if (boundary) {
      observedReturns.push(boundary.position);
      assert.deepEqual(boundary.steps, steps);
      assert.equal(boundary.before + boundary.after, digits);
      assert.equal(boundary.before.length, boundary.afterDigits);
      assert.equal(boundary.steps[boundary.afterDigits - 1]!.nextRemainder, 1n);
      assert.equal(boundary.copy, observedReturns.length);
    } else {
      assert.ok(steps.every(step => step.nextRemainder !== 1n));
    }
  }
  assert.deepEqual(expectedReturns, [166, 332, 498, 664, 830, 996]);
  assert.deepEqual(observedReturns, expectedReturns);
});

test("decimal endings split the word after one, two, or three digits and retain subsequent zeros", () => {
  const rows = recurrenceTrace({ base: 1000n, coefficients: [3n] }, 332).rows;
  for (const [index, before, after, endRemainder] of [
    [55, "7", "00", 100n], [110, "67", "0", 10n], [165, "667", "", 1n],
    [221, "7", "00", 100n], [276, "67", "0", 10n], [331, "667", "", 1n],
  ] as const) {
    const boundary = decimalReturn997(rows[index]!)!;
    assert.equal(boundary.before, before);
    assert.equal(boundary.after, after);
    assert.equal(boundary.steps.at(-1)!.nextRemainder, endRemainder);
  }
  const first = decimalReturn997(rows[55]!)!;
  assert.deepEqual(first.steps, [
    { position: 166, digit: 7n, remainder: 698n, nextRemainder: 1n },
    { position: 167, digit: 0n, remainder: 1n, nextRemainder: 10n },
    { position: 168, digit: 0n, remainder: 10n, nextRemainder: 100n },
  ]);
  assert.equal(decimalReturn997(rows[54]!), null);
  assert.equal(decimalReturn997(rows[56]!), null);
  assert.equal(decimalReturn997(rows[6]!), null);
});

test("a decimal annotation rejects a row that disagrees with its digitwise arithmetic", () => {
  const row = recurrenceTrace({ base: 1000n, coefficients: [3n] }, 56).rows[55]!;
  assert.throws(() => decimalReturn997({ ...row, word: 701n }), /agree/);
  assert.throws(() => decimalReturn997({ ...row, nextRemainder: 1n }), /agree/);
  assert.throws(() => decimalReturn997({ ...row, index: 54 }), /166-digit/);
  assert.throws(() => decimalReturn997({ ...row, index: 332 }), RangeError);
});
