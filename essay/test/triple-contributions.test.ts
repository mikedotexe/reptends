import test from "node:test";
import assert from "node:assert/strict";
import { recurrenceTrace } from "../src/math/lifts.ts";
import { certifiedPrefix } from "../src/math/unfolded-notation.ts";
import { enumerateTriplePlane, tripleCoefficient } from "../src/math/triple-contributions.ts";

test("triple planes start with two empty positions, then triangular counts", () => {
  const planes = Array.from({ length: 8 }, (_, index) => enumerateTriplePlane(index + 1));
  assert.deepEqual(planes.map(plane => plane.coefficient), [0n, 0n, 1n, 3n, 6n, 10n, 15n, 21n]);
  assert.deepEqual(planes[2]!.points, [{ i: 1, j: 1, k: 1 }]);
  assert.deepEqual(planes[3]!.points, [
    { i: 1, j: 1, k: 2 }, { i: 1, j: 2, k: 1 }, { i: 2, j: 1, k: 1 },
  ]);
  assert.equal(planes.reduce((count, plane) => count + plane.points.length, 0), 56);
  assert.equal(planes.reduce((count, plane) => count + plane.coefficient, 0n), 56n);
});

test("all 64 supported planes contain exactly their complete ordered positive triples", () => {
  for (let place = 1; place <= 64; place += 1) {
    const plane = enumerateTriplePlane(place);
    const actual = new Set(plane.points.map(point => `${point.i},${point.j},${point.k}`));
    assert.equal(actual.size, plane.points.length);
    assert.equal(BigInt(actual.size), tripleCoefficient(BigInt(place)));
    for (const point of plane.points) {
      assert(Number.isInteger(point.i) && point.i > 0);
      assert(Number.isInteger(point.j) && point.j > 0);
      assert(Number.isInteger(point.k) && point.k > 0);
      assert.equal(point.i + point.j + point.k, place);
    }
    // A separately bounded cube scan confirms no positive solution was omitted.
    for (let i = 1; i < place; i += 1) {
      for (let j = 1; j < place; j += 1) {
        const k = place - i - j;
        if (k > 0) assert(actual.has(`${i},${j},${k}`));
      }
    }
  }
});

test("permuting any of the three factors preserves each plane", () => {
  for (let place = 3; place <= 32; place += 1) {
    const plane = enumerateTriplePlane(place);
    const keys = new Set(plane.points.map(point => `${point.i},${point.j},${point.k}`));
    for (const { i, j, k } of plane.points) {
      for (const permutation of [[i, j, k], [i, k, j], [j, i, k], [j, k, i], [k, i, j], [k, j, i]]) {
        assert(keys.has(permutation.join(",")));
      }
    }
  }
});

test("plane metadata preserves exact weights without choosing or rounding a radix", () => {
  for (let place = 1; place <= 8; place += 1) {
    const plane = enumerateTriplePlane(place);
    assert.equal(plane.place, place);
    assert.deepEqual(plane.perPointWeight, { numerator: 1n, radixExponent: place });
    for (const base of [10n, 100n, 10000n]) {
      const denominator = base ** BigInt(plane.perPointWeight.radixExponent);
      assert.equal(denominator, base ** BigInt(place));
      assert.equal(plane.perPointWeight.numerator * BigInt(plane.points.length), plane.coefficient);
    }
  }
});

test("triple counts match the cubic recurrence and the initial base-10000 words", () => {
  const trace = recurrenceTrace({ base: 10000n, coefficients: [3n, -3n, 1n] }, 64);
  assert.equal(trace.denominator, 9999n ** 3n);
  assert.equal(trace.firstChangedIndex, null);
  for (const row of trace.rows) {
    const plane = enumerateTriplePlane(row.index + 1);
    assert.equal(plane.coefficient, row.raw);
    assert.equal(plane.coefficient, row.word);
  }
  assert.deepEqual(trace.rows.slice(0, 8).map(row => row.word), [0n, 0n, 1n, 3n, 6n, 10n, 15n, 21n]);
});

test("plane counts do not remain equal to printed words after carrying", () => {
  const cases = [
    { base: 10n, index: 4, raw: 6n, word: 7n },
    { base: 100n, index: 14, raw: 91n, word: 92n },
    { base: 10000n, index: 141, raw: 9870n, word: 9871n },
  ];
  for (const item of cases) {
    const trace = recurrenceTrace({ base: item.base, coefficients: [3n, -3n, 1n] }, item.index + 2);
    assert.equal(trace.firstChangedIndex, item.index);
    const boundary = trace.rows[item.index]!;
    assert.equal(tripleCoefficient(BigInt(item.index + 1)), item.raw);
    assert.equal(boundary.raw, item.raw);
    assert.equal(boundary.word, item.word);
    assert(boundary.raw < item.base);
    assert.equal(boundary.carryIn, 1n);
    assert.equal(boundary.currentStripAdjustment, 0n);
  }
});

test("a finite plane stack retains the exact residual instead of claiming a full fraction", () => {
  for (const base of [10n, 100n, 10000n]) {
    const trace = recurrenceTrace({ base, coefficients: [3n, -3n, 1n] }, 8);
    let weightedPlaneCount = 0n;
    for (let place = 1; place <= 8; place += 1) {
      const plane = enumerateTriplePlane(place);
      weightedPlaneCount += BigInt(plane.points.length) * base ** BigInt(8 - place);
    }
    const certificate = certifiedPrefix(trace, 8);
    assert.equal(certificate.prefix.numerator, weightedPlaneCount);
    assert.equal(certificate.prefix.denominator, base ** 8n);
    assert(certificate.residual.numerator > 0n);
    assert.equal(trace.denominator * weightedPlaneCount + certificate.stateAfterPrefix, base ** 8n);
  }
});

test("coefficient arithmetic stays exact well beyond floating-point integer precision", () => {
  const place = 1000000000000000000000000000000n;
  const count = tripleCoefficient(place);
  assert(count > BigInt(Number.MAX_SAFE_INTEGER));
  assert.equal(count, (place - 1n) * (place - 2n) / 2n);
  assert.equal(tripleCoefficient(place + 1n) - count, place - 1n);
  assert.equal(tripleCoefficient(place + 2n) - 2n * tripleCoefficient(place + 1n) + count, 1n);
});

test("enumeration bounds reject invalid or accidentally huge loops", () => {
  for (const place of [0, -1, 1.5, 65, 1000000, Number.NaN, Number.POSITIVE_INFINITY, Number.MAX_SAFE_INTEGER + 1]) {
    assert.throws(() => enumerateTriplePlane(place), RangeError);
  }
  assert.throws(() => tripleCoefficient(0n), RangeError);
  assert.throws(() => tripleCoefficient(-1n), RangeError);
  assert.equal(enumerateTriplePlane(64).points.length, 1953);
  assert.equal(tripleCoefficient(65n), 2016n);
});
