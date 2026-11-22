import test from "node:test";
import assert from "node:assert/strict";
import { powerFamily, regroup997 } from "../src/math/power-dial.ts";

/** Independent ordinary decimal long division, with grouping performed last. */
function decimalGroups(denominator: number, width: number, count: number): string[] {
  let state = 1n;
  let digits = "";
  for (let i = 0; i < width * count; i++) {
    const scaled = 10n * state;
    digits += String(scaled / BigInt(denominator));
    state = scaled % BigInt(denominator);
  }
  return Array.from({ length: count }, (_, i) => digits.slice(i * width, (i + 1) * width));
}

test("every fixed-gap opening and first carry agrees with decimal long division", () => {
  for (let width = 2; width <= 6; width++) {
    const r = powerFamily(width);
    assert.equal(r.denominator, 10 ** width - 3);
    assert.equal(r.quotient, 1);
    assert.equal(r.remainder, 3);
    assert.deepEqual(r.groups, decimalGroups(r.denominator, width, r.groups.length));
    assert.equal(r.firstChangedPosition, r.cleanCount + 1);
    assert.equal(r.groups.length, r.firstChangedPosition);
    for (let i = 0; i < r.cleanCount; i++) assert.equal(Number(r.groups[i]), 3 ** i);
    assert.notEqual(r.actual, r.expected);
    assert.equal(r.actual, Number(r.groups.at(-1)));
    assert.equal(r.expected, 3 ** r.cleanCount);
    assert(3 ** r.cleanCount < r.denominator);
    assert(r.nextPower >= r.denominator);
    assert.equal(r.carry, Number(BigInt(r.nextPower) / BigInt(r.denominator)));
    assert.equal(r.expected + r.carry, r.actual);
  }
});

test("the power dial exposes the predicted first changes and lengthening openings", () => {
  const expected = [
    [2, 4, 81, 83, 2],
    [3, 6, 729, 731, 2],
    [4, 8, 6561, 6562, 1],
    [5, 10, 59049, 59050, 1],
    [6, 12, 531441, 531442, 1],
  ];
  for (const [width, clean, before, after, carry] of expected) {
    const r = powerFamily(width!);
    assert.deepEqual([r.cleanCount, r.expected, r.actual, r.carry], [clean, before, after, carry]);
    assert(r.expected < r.base, "The first changed coefficient still fits in its group.");
  }
});

test("integer field members are independently bracketed at every displayed power", () => {
  const expected = [[91, 110, 20], [969, 1032, 64], [9901, 10100, 200],
    [99685, 100316, 632], [999001, 1001000, 2000]];
  for (let width = 2; width <= 6; width++) {
    const { base, field: f } = powerFamily(width);
    assert.deepEqual([f.first, f.last, f.count], expected[width - 2]);
    const isMember = (n: number) => (BigInt(base) - BigInt(n)) ** 2n < BigInt(n);
    assert(!isMember(f.first - 1));
    assert(!isMember(f.last + 1));
    for (let n = f.first; n <= f.last; n++) assert(isMember(n));
    assert(f.first - 1 < f.lower && f.lower < f.first);
    assert(f.last < f.upper && f.upper < f.last + 1);
    assert(Math.abs(f.upperRoot - f.lowerRoot - 1) < 1e-12);
    assert(Math.abs(f.lowerRoot * f.upperRoot - base) < 1e-8);
    assert(Math.abs(f.lowerRoot ** 2 - f.lower) < 1e-8);
    assert(Math.abs(f.upperRoot ** 2 - f.upper) < 1e-8);
    assert(Math.abs(f.ordinaryWidth - (f.upper - f.lower)) < 1e-8);
  }
});

test("regrouping 997 changes the quotient and multiplier, not the decimal digits", () => {
  const expected = [
    [3, 1, 3, 6, 729, 731],
    [4, 10, 30, 2, 9000, 9027],
    [5, 100, 300, 1, 30000, 30090],
    [6, 1003, 9, 3, 731187, 731193],
  ];
  const shared = decimalGroups(997, 1, 60).join("");
  for (const [width, quotient, remainder, clean, before, after] of expected) {
    const r = regroup997(width!);
    assert.equal(r.denominator, 997);
    assert.deepEqual([r.quotient, r.remainder, r.cleanCount, r.expected, r.actual],
      [quotient, remainder, clean, before, after]);
    assert.equal(r.base, r.quotient * r.denominator + r.remainder);
    assert.deepEqual(r.groups, decimalGroups(997, width!, r.groups.length));
    assert.deepEqual(r.tapeGroups, decimalGroups(997, width!, 60 / width!));
    assert.equal(r.tapeGroups.join(""), shared);
    assert(r.tapeGroups.every(group => group.length === width));
    for (let i = 0; i < r.cleanCount; i++) assert.equal(Number(r.groups[i]), r.coefficients[i]);
    assert.equal(r.carry, Number(BigInt(r.remainder) ** BigInt(r.firstChangedPosition) / 997n));
    assert.equal(r.expected + r.carry, r.actual);
    assert(r.coefficients.every(Number.isSafeInteger));
  }
  assert.deepEqual(regroup997(6).coefficients.slice(0, 3), [1003, 9027, 81243]);
});

test("both dials reject fractions, non-finite values, and unsupported widths", () => {
  for (const width of [NaN, Infinity, -Infinity, 0, 1, 2.5, 7, Number.MAX_SAFE_INTEGER]) {
    assert.throws(() => powerFamily(width), RangeError);
  }
  for (const width of [NaN, Infinity, -Infinity, 0, 2, 3.5, 7, Number.MAX_SAFE_INTEGER]) {
    assert.throws(() => regroup997(width), RangeError);
  }
});
