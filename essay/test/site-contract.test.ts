import test from "node:test";
import assert from "node:assert/strict";
import { formatWord, recurrenceTrace } from "../src/math/lifts.ts";
import { certifiedPrefix } from "../src/math/unfolded-notation.ts";
import { enumerateTriplePlane } from "../src/math/triple-contributions.ts";

const geometric = { base: 1000n, coefficients: [3n] };

test("all 332 displayed transitions and both readouts agree with independent division", () => {
  const trace = recurrenceTrace(geometric, 332);
  let ordinaryRemainder = 1n;
  let baseThreeRemainder = 1n;
  let growingPower = 1n;
  for (const row of trace.rows) {
    const scaled = 1000n * ordinaryRemainder;
    assert.equal(row.lift, growingPower);
    assert.equal(row.remainder, ordinaryRemainder);
    assert.equal(row.word, scaled / 997n);
    assert.equal(row.nextRemainder, scaled % 997n);
    const localWraps = (3n * ordinaryRemainder) / 997n;
    const baseThreeShifted = 3n * baseThreeRemainder;
    const baseThreeDigit = baseThreeShifted / 997n;
    assert(baseThreeDigit >= 0n && baseThreeDigit <= 2n);
    assert.equal(row.remainder, baseThreeRemainder);
    assert.equal(localWraps, baseThreeDigit);
    assert.equal(row.nextRemainder, baseThreeShifted % 997n);
    assert.equal(row.word, ordinaryRemainder + localWraps);
    assert.equal(row.carryIn, 3n * growingPower / 997n);
    ordinaryRemainder = scaled % 997n;
    baseThreeRemainder = baseThreeShifted % 997n;
    growingPower *= 3n;
  }
  assert.deepEqual(trace.rows.slice(6, 9).map(row => ({
    remainder: row.remainder,
    baseThreeDigit: (3n * row.remainder) / 997n,
    word: row.word,
    nextRemainder: row.nextRemainder,
  })), [
    { remainder: 729n, baseThreeDigit: 2n, word: 731n, nextRemainder: 193n },
    { remainder: 193n, baseThreeDigit: 0n, word: 193n, nextRemainder: 579n },
    { remainder: 579n, baseThreeDigit: 1n, word: 580n, nextRemainder: 740n },
  ]);
  const boundary = trace.rows[6]!;
  assert.equal(formatWord(boundary.word, trace.base), "731");
  assert.equal(boundary.raw, 729n);
  assert.equal(boundary.nextLift, 2187n);
  assert.equal(boundary.nextRemainder, 193n);
  const following = trace.rows[7]!;
  assert.equal(following.raw + following.carryIn + following.currentStripAdjustment, 193n);
  assert.equal(following.carryIn, 6n);
  assert.equal(following.currentStripAdjustment, -2000n);
});

test("all 333 finite boundaries preserve the exact rational value", () => {
  const trace = recurrenceTrace(geometric, 332);
  let ordinaryPrefix = 0n;
  for (let terms = 0; terms <= 332; terms += 1) {
    if (terms > 0) ordinaryPrefix = 1000n * ordinaryPrefix + trace.rows[terms - 1]!.word;
    const certificate = certifiedPrefix(trace, terms);
    const scale = 1000n ** BigInt(terms);
    assert.equal(certificate.prefix.denominator, scale);
    assert.equal(certificate.prefix.numerator * 997n + certificate.stateAfterPrefix, scale);
    assert.equal(certificate.settledPrefixInteger, ordinaryPrefix);
    assert.equal(997n * ordinaryPrefix + certificate.canonicalRemainder, scale);
    assert.equal(certificate.prefix.numerator + certificate.boundaryCarry, ordinaryPrefix);
  }
});

test("1/997 returns after 166 groups; their 498 digits contain three minimal decimal periods", () => {
  function firstReturn(base: bigint): number {
    let remainder = 1n;
    const seen = new Set<bigint>();
    for (let steps = 1; steps <= 997; steps += 1) {
      assert(!seen.has(remainder), "An orbit must not enter a different cycle before returning.");
      seen.add(remainder);
      remainder = base * remainder % 997n;
      if (remainder === 1n) return steps;
    }
    throw new Error("The expected complete orbit was not found.");
  }
  assert.equal(firstReturn(1000n), 166);
  assert.equal(firstReturn(10n), 166);
  const trace = recurrenceTrace(geometric, 332);
  let decimalRemainder = 1n;
  let decimalPeriod = "";
  for (let position = 0; position < 166; position += 1) {
    const shifted = decimalRemainder * 10n;
    decimalPeriod += String(shifted / 997n);
    decimalRemainder = shifted % 997n;
  }
  const groupedPeriod = trace.rows.slice(0, 166).map(row => formatWord(row.word, 1000n)).join("");
  assert.equal(groupedPeriod.length, 498);
  assert.equal(groupedPeriod, decimalPeriod.repeat(3));
  for (let index = 0; index < 166; index += 1) {
    const first = trace.rows[index]!;
    const returned = trace.rows[index + 166]!;
    assert.equal(returned.remainder, first.remainder);
    assert.equal((3n * returned.remainder) / 997n, (3n * first.remainder) / 997n);
    assert.equal(returned.word, first.word);
    assert.equal(returned.lift, first.lift * 3n ** 166n);
  }
  assert.equal(trace.rows[172]!.lift.toString().length, 83);
});

test("square and cube counts retain empty places and represent ordered contributions", () => {
  for (const base of [100n, 1000n, 10000n]) {
    const square = recurrenceTrace({ base, coefficients: [2n, -1n] }, 12);
    const cube = recurrenceTrace({ base, coefficients: [3n, -3n, 1n] }, 12);
    assert.deepEqual(square.rows.slice(0, 5).map(row => row.raw), [0n, 1n, 2n, 3n, 4n]);
    assert.deepEqual(cube.rows.slice(0, 6).map(row => row.raw), [0n, 0n, 1n, 3n, 6n, 10n]);
    for (let place = 1; place <= 12; place += 1) {
      let pairCount = 0;
      for (let i = 1; i < place; i += 1) {
        const j = place - i;
        if (j >= 1) pairCount += 1;
      }
      assert.equal(square.rows[place - 1]!.raw, BigInt(pairCount));
      assert.equal(cube.rows[place - 1]!.raw, enumerateTriplePlane(place).coefficient);
    }
  }
});
