import test from "node:test";
import assert from "node:assert/strict";
import { recurrenceTrace } from "../src/math/lifts.ts";
import { buildUnfoldedView, certifiedPrefix } from "../src/math/unfolded-notation.ts";

test("1/997: display growth is separate from the earlier carry boundary", () => {
  const view = buildUnfoldedView({ base: 1000n, coefficients: [3n] });
  assert.equal(view.minimumDisplayWidth, 3);
  assert.equal(view.trace.base, 1000n);
  assert.equal(view.rows.length, 16);
  assert.deepEqual(view.rows.slice(0, 8).map(row => row.displayedTerm),
    ["001", "003", "009", "027", "081", "243", "729", "2187"]);
  assert.equal(view.trace.firstChangedIndex, 6);
  assert.equal(view.rows[6]!.widthMarker, null);
  assert.equal(view.rows[6]!.word, 731n);
  assert.equal(view.rows[7]!.widthMarker, 4);
  assert.equal(view.rows[7]!.placeIndex, 8);
  assert.equal(view.rows[8]!.widthMarker, null);
  assert.equal(view.rows[9]!.widthMarker, 5);
  for (const row of view.rows) {
    assert.equal(row.placeIndex, row.index + 1);
    assert.equal(row.raw, 3n ** BigInt(row.index));
    assert.deepEqual(row.polynomial, view.trace.rows[row.index]!.polynomial);
  }
});

test("1/9997 announces five-digit terms without changing the 10000 weight", () => {
  const view = buildUnfoldedView({ base: 10000n, coefficients: [3n] }, 12);
  assert.equal(view.trace.denominator, 9997n);
  assert.equal(view.minimumDisplayWidth, 4);
  assert.equal(view.rows[0]!.displayedTerm, "0001");
  assert.equal(view.rows[8]!.widthMarker, null);
  assert.equal(view.rows[8]!.word, 6562n);
  assert.equal(view.rows[9]!.widthMarker, 5);
  assert.equal(view.rows[9]!.displayedTerm, "19683");
  assert.equal(view.rows[9]!.placeIndex, 10);
});

test("1/19997 has base 20000, not an invented decimal grouping width", () => {
  const view = buildUnfoldedView({ base: 20000n, coefficients: [3n] }, 10);
  assert.equal(view.trace.denominator, 19997n);
  assert.equal(view.minimumDisplayWidth, 1);
  assert.equal(view.rows[0]!.displayedTerm, "1");
  assert.equal(view.rows[3]!.widthMarker, 2);
  assert.equal(view.rows[7]!.widthMarker, 4);
  assert.equal(certifiedPrefix(view.trace, 7).prefix.denominator, 20000n ** 7n);
});

test("Fibonacci preserves seeded zero and grows its labels independently", () => {
  const view = buildUnfoldedView({ base: 100n, coefficients: [1n, 1n] }, 15);
  assert.deepEqual(view.rows.slice(0, 4).map(row => row.displayedTerm), ["00", "01", "01", "02"]);
  assert.equal(view.rows[11]!.raw, 89n);
  assert.equal(view.rows[11]!.word, 90n);
  assert.equal(view.rows[11]!.widthMarker, null);
  assert.equal(view.rows[12]!.raw, 144n);
  assert.equal(view.rows[12]!.widthMarker, 3);
});

test("signed labels count magnitude digits, not the minus sign", () => {
  const view = buildUnfoldedView({ base: 100n, coefficients: [-1n, 1n] }, 15);
  assert.deepEqual(view.rows.slice(0, 7).map(row => row.displayedTerm),
    ["00", "01", "−01", "02", "−03", "05", "−08"]);
  assert.equal(view.rows[12]!.raw, -144n);
  assert.equal(view.rows[12]!.displayWidth, 3);
  assert.equal(view.rows[12]!.widthMarker, 3);
});

test("a width announcement is a record, not a repeat after a smaller term", () => {
  const view = buildUnfoldedView({ base: 10n, coefficients: [0n, -100n] }, 8);
  assert.deepEqual(view.rows.map(row => row.raw), [0n, 1n, 0n, -100n, 0n, 10000n, 0n, -1000000n]);
  assert.deepEqual(view.rows.map(row => row.widthMarker), [null, null, null, 3, null, 5, null, 7]);
  assert.equal(view.rows[4]!.displayWidth, 1);
  assert.equal(view.rows[4]!.displayedTerm, "0");
});

test("finite certificates keep exact fixed weights and the unresolved balance", () => {
  const trace = recurrenceTrace({ base: 1000n, coefficients: [3n] }, 20);
  const certificate = certifiedPrefix(trace, 2);
  assert.deepEqual(certificate.prefix, { numerator: 1003n, denominator: 1000000n });
  assert.deepEqual(certificate.residual, { numerator: 9n, denominator: 997000000n });
  assert.deepEqual(certificate.original, { numerator: 1n, denominator: 997n });
  assert.deepEqual(certificate.identity, { left: 1000000n, right: 1000000n });
  assert.equal(certificate.stateAfterPrefix, 9n);
  assert.equal(certificate.boundaryCarry, 0n);
  assert.equal(certificate.settledPrefixInteger, 1003n);
  assert.equal(certificate.canonicalRemainder, 9n);
  const firstCarry = certifiedPrefix(trace, 7);
  assert.equal(firstCarry.boundaryCarry, 2n);
  assert.equal(firstCarry.settledPrefixInteger, 1003009027081243731n);
  assert.equal(firstCarry.canonicalRemainder, 193n);
  const empty = certifiedPrefix(trace, 0);
  assert.deepEqual(empty.prefix, { numerator: 0n, denominator: 1n });
  assert.deepEqual(empty.residual, { numerator: 1n, denominator: 997n });
});

test("every finite prefix certifies geometric, Fibonacci, signed and divergent cases", () => {
  const specifications = [
    { base: 1000n, coefficients: [3n] },
    { base: 10000n, coefficients: [3n], numerator: 9n },
    { base: 20000n, coefficients: [3n] },
    { base: 100n, coefficients: [1n, 1n] },
    { base: 100n, coefficients: [-1n, 1n] },
    { base: 100n, coefficients: [2n, -1n] },
    { base: 10n, coefficients: [-20n] },
  ];
  for (const spec of specifications) {
    const trace = recurrenceTrace(spec, 40);
    let independentNumerator = 0n;
    let independentPower = 1n;
    let independentSettledPrefix = 0n;
    for (let terms = 0; terms <= trace.rows.length; terms += 1) {
      const certificate = certifiedPrefix(trace, terms);
      assert.equal(certificate.prefix.numerator, independentNumerator);
      assert.equal(certificate.prefix.denominator, independentPower);
      assert.equal(certificate.identity.left, certificate.identity.right);
      assert.equal(certificate.identity.right, trace.numerator * independentPower);
      assert.equal(certificate.residual.denominator, trace.denominator * independentPower);
      assert.equal(certificate.settledPrefixInteger, independentSettledPrefix);
      assert.equal(certificate.settledPrefixInteger, trace.numerator * independentPower / trace.denominator);
      assert.equal(certificate.canonicalRemainder, trace.numerator * independentPower % trace.denominator);
      assert.equal(certificate.prefix.numerator + certificate.boundaryCarry, independentSettledPrefix);
      if (terms < trace.rows.length) {
        independentNumerator = trace.base * independentNumerator + trace.rows[terms]!.raw;
        independentSettledPrefix = trace.base * independentSettledPrefix + trace.rows[terms]!.word;
        independentPower *= trace.base;
      }
    }
  }
  const divergent = recurrenceTrace({ base: 10n, coefficients: [-20n] }, 8);
  const first = certifiedPrefix(divergent, 1);
  assert.deepEqual(first.prefix, { numerator: 1n, denominator: 10n });
  assert.deepEqual(first.residual, { numerator: -20n, denominator: 300n });
  const later = certifiedPrefix(divergent, 8);
  assert(later.residual.numerator > later.residual.denominator);
  assert.equal(later.identity.left, later.identity.right);
});

test("empty views and finite-prefix input checks are explicit", () => {
  const view = buildUnfoldedView({ base: 1000n, coefficients: [3n] }, 0);
  assert.deepEqual(view.rows, []);
  assert.equal(view.minimumDisplayWidth, 3);
  assert.equal(certifiedPrefix(view.trace, 0).stateAfterPrefix, 1n);
  for (const count of [-1, 0.5, 1, Number.NaN, Number.POSITIVE_INFINITY]) {
    assert.throws(() => certifiedPrefix(view.trace, count), RangeError);
  }
  assert.throws(() => buildUnfoldedView({ base: 1000n, coefficients: [3n] }, -1), RangeError);
  assert.throws(() => buildUnfoldedView({ base: 1000n, coefficients: [3n] }, 100001), RangeError);
  const trace = recurrenceTrace({ base: 1000n, coefficients: [3n] }, 1);
  const inconsistentTrace = { ...trace, numerator: 2n };
  assert.throws(() => certifiedPrefix(inconsistentTrace, 1), /do not equal/);
});
