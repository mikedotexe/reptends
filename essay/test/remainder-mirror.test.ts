import test from "node:test";
import assert from "node:assert/strict";
import { MIRROR_PAIRS, mirrorPair997 } from "../src/remainder-mirror.ts";

test("all mirror pairs agree with an independent decimal walk, including entering and outgoing states", () => {
  let r = 1n;
  const decimal: { before: bigint; digit: bigint; after: bigint }[] = [];
  for (let i = 0; i < 498; i++) {
    const before = r;
    const digit = 10n * r / 997n;
    r = 10n * r % 997n;
    decimal.push({ before, digit, after: r });
  }
  assert.equal(MIRROR_PAIRS, 83);
  for (let i = 0; i < MIRROR_PAIRS; i++) {
    const { first, second } = mirrorPair997(i);
    for (const row of [first, second]) {
      const digits = decimal.slice(3 * row.index, 3 * row.index + 3);
      assert.equal(row.remainder, digits[0]!.before);
      assert.equal(row.word, digits.reduce((n, d) => 10n * n + d.digit, 0n));
      assert.equal(row.nextRemainder, digits[2]!.after);
    }
    assert.equal(first.remainder + second.remainder, 997n);
    assert.equal(first.word + second.word, 999n);
    assert.equal(first.nextRemainder + second.nextRemainder, 997n);
  }
  assert.equal(mirrorPair997(6).first.word, 731n);
  assert.equal(mirrorPair997(6).second.word, 268n);
});

test("the first antipode ends group 83 and the first return ends group 166", () => {
  const rows = Array.from({ length: 83 }, (_, i) => mirrorPair997(i));
  assert(rows.slice(0, -1).every(({ first }) => first.nextRemainder !== 996n));
  assert.equal(rows.at(-1)!.first.nextRemainder, 996n);
  assert.equal(rows[0]!.second.word, 998n);
  assert.equal(rows.at(-1)!.second.nextRemainder, 1n);
  assert.equal(rows.at(-1)!.second.word, 667n);
  assert(rows.flatMap(pair => [pair.first, pair.second]).filter(row => row.index < 165).every(row => row.nextRemainder !== 1n));
  for (const invalid of [-1, 83, 0.5, NaN]) assert.throws(() => mirrorPair997(invalid), RangeError);
});

test("six decimal steps for one seventh pack into a single repeated digit with the same value", () => {
  let remainder = 1n;
  let packed = 0n;
  for (let i = 0; i < 6; i++) {
    const scaled = 10n * remainder;
    packed = 10n * packed + scaled / 7n;
    remainder = scaled % 7n;
    if (i < 5) assert.notEqual(remainder, 1n);
  }
  assert.equal(packed, 142857n);
  assert.equal(remainder, 1n);
  assert.equal(1000000n, 7n * packed + remainder);
  assert.equal(7n * packed, 1000000n - 1n);
});
