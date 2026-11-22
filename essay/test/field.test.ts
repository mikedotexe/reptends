import test from "node:test";
import assert from "node:assert/strict";
import { coordinate, fieldReading, THOUSAND_FIELD } from "../src/math/field.ts";

/** Independent decimal-digit walk, regrouped only after all digits are emitted. */
function decimalGroups(n: number): string[] {
  const denominator = BigInt(n);
  let remainder = 1n;
  let digits = "";
  for (let i = 0; i < 18; i++) {
    const scaled = 10n * remainder;
    digits += String(scaled / denominator);
    remainder = scaled % denominator;
  }
  return digits.match(/.{3}/g)!;
}

test("every displayed reciprocal agrees with independent decimal division", () => {
  const members: number[] = [];
  for (let n = 968; n <= 1033; n++) {
    const reading = fieldReading(n);
    assert.deepEqual(reading.groups, decimalGroups(n), `1/${n}`);
    assert.equal(reading.actualSecond, Number(reading.groups[1]));
    // At these denominators the first word already agrees. The field boundary
    // is precisely where the second predicted word also survives unchanged.
    assert.equal(reading.inField, reading.expectedSecond === reading.actualSecond, `1/${n}`);
    if (reading.inField) members.push(n);
  }
  assert.equal(members.length, 64);
  assert.equal(members[0], 969);
  assert.equal(members.at(-1), 1032);
});

test("both sides show the last member and its first excluded neighbour", () => {
  const lowerOutside = fieldReading(968);
  assert.equal(lowerOutside.expectedSecond, 32);
  assert.deepEqual(lowerOutside.groups.slice(0, 2), ["001", "033"]);
  assert.equal(lowerOutside.inField, false);
  assert.deepEqual(fieldReading(969).groups.slice(0, 2), ["001", "031"]);
  assert.equal(fieldReading(969).inField, true);
  assert.deepEqual(fieldReading(1032).groups.slice(0, 2), ["000", "968"]);
  assert.equal(fieldReading(1032).inField, true);
  const upperOutside = fieldReading(1033);
  assert.equal(upperOutside.expectedSecond, 967);
  assert.deepEqual(upperOutside.groups.slice(0, 2), ["000", "968"]);
  assert.equal(upperOutside.inField, false);
});

test("signed coefficients stay distinct from borrowed words and terminating expansions", () => {
  assert.deepEqual(fieldReading(997).signedTerms, [1, 3, 9, 27, 81, 243]);
  assert.deepEqual(fieldReading(997).groups, ["001", "003", "009", "027", "081", "243"]);
  assert.deepEqual(fieldReading(1003).signedTerms, [1, -3, 9, -27, 81, -243]);
  assert.deepEqual(fieldReading(1003).groups, ["000", "997", "008", "973", "080", "757"]);
  assert.deepEqual(fieldReading(1000).groups, ["001", "000", "000", "000", "000", "000"]);
  assert.deepEqual(fieldReading(1024).groups, ["000", "976", "562", "500", "000", "000"]);
  assert.equal(fieldReading(1000).inField, true);
  assert.equal(fieldReading(1024).inField, true);
});

test("continuous edges have a unit square-root gap and bracket 64 integer members", () => {
  const f = THOUSAND_FIELD;
  assert(Math.abs(f.upperRoot - f.lowerRoot - 1) < 1e-12);
  assert(Math.abs(f.lowerRoot * f.upperRoot - 1000) < 1e-10);
  assert(Math.abs(f.lowerRoot ** 2 - f.lower) < 1e-10);
  assert(Math.abs(f.upperRoot ** 2 - f.upper) < 1e-10);
  for (const edge of [f.lower, f.upper]) assert(Math.abs((1000 - edge) ** 2 - edge) < 1e-9);
  assert(968 < f.lower && f.lower < f.first);
  assert(f.last < f.upper && f.upper < 1033);
  assert.equal(f.count, f.last - f.first + 1);
});

test("plot scales preserve order and allow continuous boundaries between dots", () => {
  for (const scale of ["number", "root"] as const) {
    assert.equal(coordinate(968, scale), 0);
    assert.equal(coordinate(1033, scale), 1);
    for (let n = 969; n <= 1033; n++) assert(coordinate(n - 1, scale) < coordinate(n, scale));
    assert(coordinate(968, scale) < coordinate(THOUSAND_FIELD.lower, scale));
    assert(coordinate(THOUSAND_FIELD.lower, scale) < coordinate(969, scale));
    assert(coordinate(1032, scale) < coordinate(THOUSAND_FIELD.upper, scale));
    assert(coordinate(THOUSAND_FIELD.upper, scale) < coordinate(1033, scale));
  }
  assert.notEqual(coordinate(997, "number"), coordinate(997, "root"));
});

test("the lesson rejects values outside its bounded arithmetic and plotting domains", () => {
  for (const n of [967, 1034, 997.5, NaN, Infinity, -Infinity]) {
    assert.throws(() => fieldReading(n), RangeError);
  }
  for (const n of [967, 1034, NaN, Infinity, -Infinity]) {
    assert.throws(() => coordinate(n, "root"), RangeError);
  }
  assert.throws(() => coordinate(997, "invalid" as "number"), RangeError);
});
