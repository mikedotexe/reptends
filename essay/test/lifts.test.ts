import test from "node:test";
import assert from "node:assert/strict";
import {
  euclideanDivide, normalizeTransition, recurrenceTrace, canonicalView,
  recurrenceDenominator, formatWord,
} from "../src/math/lifts.ts";

test("Euclidean division handles borrows and exact negative multiples", () => {
  assert.deepEqual(euclideanDivide(-99n, 10099n), { quotient: -1n, remainder: 10000n });
  assert.deepEqual(euclideanDivide(-20n, 10n), { quotient: -2n, remainder: 0n });
  assert.deepEqual(euclideanDivide(0n, 7n), { quotient: 0n, remainder: 0n });
  assert.throws(() => euclideanDivide(5n, 0n), RangeError);
  assert.throws(() => euclideanDivide(5n, -1n), RangeError);
});

test("1/997: 729 becomes 731 while the raw power still fits", () => {
  const trace = recurrenceTrace({ base: 1000n, coefficients: [3n] }, 60);
  assert.equal(trace.denominator, 997n);
  assert.equal(trace.firstChangedIndex, 6);
  assert.deepEqual(trace.rows.slice(0, 10).map(row => row.word), [1n, 3n, 9n, 27n, 81n, 243n, 731n, 193n, 580n, 742n]);
  const row = trace.rows[6]!;
  assert.equal(row.raw, 729n);
  assert.equal(row.carryIn, 2n);
  assert.equal(row.currentStripAdjustment, 0n);
  assert.equal(row.nextRemainder, 193n);
  assert(trace.rows[59]!.lift > BigInt(Number.MAX_SAFE_INTEGER));
});

test("Fibonacci, early tail carry, and signed-borrow boundaries", () => {
  const cases = [
    { base: 100n, coefficients: [1n, 1n], exit: 11, raw: 89n, word: 90n },
    { base: 1000n, coefficients: [1n, 1n], exit: 16, raw: 987n, word: 988n },
    { base: 14n, coefficients: [1n, 1n], exit: 6, raw: 8n, word: 9n },
    { base: 100n, coefficients: [-1n, 1n], exit: 1, raw: 1n, word: 0n },
  ];
  for (const item of cases) {
    const trace = recurrenceTrace(item, 25);
    assert.equal(trace.firstExitIndex, item.exit);
    assert.equal(trace.rows[item.exit]!.raw, item.raw);
    assert.equal(trace.rows[item.exit]!.word, item.word);
  }
});

test("counting reciprocals: missing word and exact restart over two cycles", () => {
  for (const base of [3n, 10n, 100n, 1000n, 10000n]) {
    const period = Number(base - 1n);
    const trace = recurrenceTrace({ base, coefficients: [2n, -1n] }, 2 * period);
    assert.equal(trace.denominator, (base - 1n) ** 2n);
    assert.equal(trace.firstChangedIndex, Number(base - 2n));
    for (const row of trace.rows) {
      const m = BigInt(row.index), s = m % (base - 1n);
      assert.equal(row.raw, m);
      assert.equal(row.lift, 1n + m * (base - 1n));
      assert.equal(row.word, s === base - 2n ? base - 1n : s);
    }
    assert.equal(trace.rows[period - 1]!.nextRemainder, 1n);
    assert.equal(trace.rows[2 * period - 1]!.nextRemainder, 1n);
  }
});

test("same orbit, different lift: arbitrary signed changes preserve all words", () => {
  const trace = recurrenceTrace({ base: 1000n, coefficients: [1n, 1n] }, 50);
  for (const row of trace.rows) {
    const canonical = canonicalView(trace.base, trace.denominator, row);
    assert.equal(canonical.raw, row.word);
    assert.equal(canonical.quotient, 0n);
    assert.equal(canonical.nextQuotient, 0n);
    assert.equal(canonical.word, row.word);
    const shifted = normalizeTransition(trace.base, trace.denominator,
      row.lift - trace.denominator * 100000000000000000003n,
      row.nextLift + trace.denominator * 999999999999999999999n);
    assert.equal(shifted.word, row.word);
    assert.equal(shifted.remainder, row.remainder);
    assert.equal(shifted.nextRemainder, row.nextRemainder);
  }
});

test("signed recurrence sweep independently preserves powers modulo D", () => {
  let configurations = 0;
  for (let base = 2n; base <= 12n; base += 1n) {
    for (let c1 = -3n; c1 <= 3n; c1 += 1n) for (let c2 = -3n; c2 <= 3n; c2 += 1n) {
      const spec = { base, coefficients: [c1, c2] };
      if (base * base - c1 * base - c2 < 2n) continue;
      for (const numerator of [1n, recurrenceDenominator(spec) - 1n]) {
        const trace = recurrenceTrace({ ...spec, numerator }, 80);
        let power = numerator;
        for (const row of trace.rows) {
          assert.equal(row.remainder, power % trace.denominator);
          power *= base;
        }
        configurations += 1;
      }
    }
  }
  assert(configurations > 900);
});

test("cubic repeated root yields raw triangular numbers, including seeded zeros", () => {
  const trace = recurrenceTrace({ base: 100n, coefficients: [3n, -3n, 1n] }, 20);
  assert.equal(trace.denominator, 99n ** 3n);
  assert.deepEqual(trace.rows.slice(0, 8).map(row => row.raw), [0n, 0n, 1n, 3n, 6n, 10n, 15n, 21n]);
});

test("non-coprime denominators and terminating orbits are supported", () => {
  const trace = recurrenceTrace({ base: 10n, coefficients: [2n] }, 12);
  assert.equal(trace.denominator, 8n);
  assert.deepEqual(trace.rows.slice(0, 5).map(row => row.word), [1n, 2n, 5n, 0n, 0n]);
});

test("finite lifts remain exact even when the raw radix series diverges", () => {
  const trace = recurrenceTrace({ base: 10n, coefficients: [-20n] }, 30);
  assert.equal(trace.denominator, 30n);
  assert.deepEqual(trace.rows.slice(0, 4).map(row => row.raw), [1n, -20n, 400n, -8000n]);
  assert.deepEqual(trace.rows.slice(0, 6).map(row => row.word), [0n, 3n, 3n, 3n, 3n, 3n]);
  assert.equal(trace.firstExitIndex, 0);
});

test("higher-degree signed states agree with independently computed modular powers", () => {
  for (let degree = 1; degree <= 6; degree += 1) {
    for (let seed = 0; seed < 20; seed += 1) {
      const base = BigInt(7 + seed);
      const coefficients = Array.from({ length: degree }, (_, j) => BigInt((seed + j * 3) % 7 - 3));
      const trace = recurrenceTrace({ base, coefficients }, 50);
      let residue = 1n;
      for (const row of trace.rows) {
        assert.equal(row.remainder, residue);
        residue = base * residue % trace.denominator;
        assert.equal(row.nextRemainder, residue);
      }
    }
  }
});

test("finite clean trace does not claim perpetual cleanliness", () => {
  const trace = recurrenceTrace({ base: 1000n, coefficients: [3n] }, 6);
  assert.equal(trace.firstChangedIndex, null);
  assert.equal(trace.firstExitIndex, null);
  assert.deepEqual(recurrenceTrace({ base: 10n, coefficients: [1n] }, 0).rows, []);
});

test("invalid inputs are rejected and word formatting keeps leading zeros", () => {
  assert.throws(() => normalizeTransition(1000n, 997n, 729n, 2188n), /same remainder orbit/);
  assert.throws(() => recurrenceTrace({ base: 1n, coefficients: [1n] }), RangeError);
  assert.throws(() => recurrenceTrace({ base: 10n, coefficients: [] }), RangeError);
  assert.throws(() => recurrenceTrace({ base: 10n, coefficients: [10n] }), RangeError);
  assert.throws(() => recurrenceTrace({ base: 10n, coefficients: [1n], numerator: 9n }), RangeError);
  assert.throws(() => recurrenceTrace({ base: 10n, coefficients: [1n], numerator: 0n }), RangeError);
  assert.throws(() => recurrenceTrace({ base: 10n, coefficients: [1n] }, 0.5), RangeError);
  assert.throws(() => recurrenceTrace({ base: 10n, coefficients: [1n] }, 100001), RangeError);
  assert.equal(formatWord(1n, 1000n), "001");
  assert.equal(formatWord(0n, 100n), "00");
  assert.equal(formatWord(13n, 14n), "[13]");
  assert.throws(() => formatWord(100n, 100n), RangeError);
});
