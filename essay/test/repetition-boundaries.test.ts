import test from "node:test";
import assert from "node:assert/strict";
import { recurrenceTrace } from "../src/math/lifts.ts";
import { certifiedPrefix } from "../src/math/unfolded-notation.ts";
import { buildRepetitionBoundary, REPETITION_BOUNDARIES } from "../src/repetition-boundaries.ts";

const fixtures = [
  { denominator: 97n, width: 2, multiplier: 3n, decimalPreperiod: 0, decimalPeriod: 96,
    groupedPreperiod: 0, groupedPeriod: 48, firstChangedIndex: 4, raw: 81n, corrected: 83n,
    decimalIndex: 47, decimalWord: "67", split: 2, groupedIndex: 47, groupedWord: "67",
    decimalBefore: 68n, decimalAfter: 1n, groupedBefore: 65n, groupedAfter: 1n },
  { denominator: 997n, width: 3, multiplier: 3n, decimalPreperiod: 0, decimalPeriod: 166,
    groupedPreperiod: 0, groupedPeriod: 166, firstChangedIndex: 6, raw: 729n, corrected: 731n,
    decimalIndex: 55, decimalWord: "700", split: 1, groupedIndex: 165, groupedWord: "667",
    decimalBefore: 698n, decimalAfter: 1n, groupedBefore: 665n, groupedAfter: 1n },
  { denominator: 94n, width: 2, multiplier: 6n, decimalPreperiod: 1, decimalPeriod: 46,
    groupedPreperiod: 1, groupedPeriod: 23, firstChangedIndex: 2, raw: 36n, corrected: 38n,
    decimalIndex: 23, decimalWord: "51", split: 1, groupedIndex: 23, groupedWord: "51",
    decimalBefore: 48n, decimalAfter: 10n, groupedBefore: 48n, groupedAfter: 6n },
  { denominator: 994n, width: 3, multiplier: 6n, decimalPreperiod: 1, decimalPeriod: 210,
    groupedPreperiod: 1, groupedPeriod: 70, firstChangedIndex: 3, raw: 216n, corrected: 217n,
    decimalIndex: 70, decimalWord: "501", split: 1, groupedIndex: 70, groupedWord: "501",
    decimalBefore: 498n, decimalAfter: 10n, groupedBefore: 498n, groupedAfter: 6n },
] as const;

for (const fixture of fixtures) {
  test(`1/${fixture.denominator}: independently detected decimal and grouped soft ends`, () => {
    const model = REPETITION_BOUNDARIES.find(item => item.denominator === fixture.denominator)!;
    assert.equal(model.width, fixture.width);
    assert.equal(model.multiplier, fixture.multiplier);
    assert.equal(model.decimal.preperiod, fixture.decimalPreperiod);
    assert.equal(model.decimal.period, fixture.decimalPeriod);
    assert.equal(model.grouped.preperiod, fixture.groupedPreperiod);
    assert.equal(model.grouped.period, fixture.groupedPeriod);
    assert.equal(model.decimal.prefix, fixture.decimalPreperiod ? "0" : "");
    assert.equal(model.decimal.cycle.length, fixture.decimalPeriod);

    assert.equal(model.firstChangedIndex, fixture.firstChangedIndex);
    assert.equal(model.lastUnchangedIndex, fixture.firstChangedIndex - 1);
    assert.equal(model.firstChangedRow.raw, fixture.raw);
    assert.equal(model.firstChangedRow.word, fixture.corrected);
    for (let index = 0; index < model.firstChangedIndex; index += 1) {
      assert.equal(model.grouped.rows[index]!.word, fixture.multiplier ** BigInt(index));
    }
    assert(fixture.raw < model.base, "The first correction arrives before the raw value outgrows its word.");
    assert(fixture.raw * fixture.multiplier >= fixture.denominator);

    const { decimalEnd, groupedEnd } = model;
    assert.equal(decimalEnd.position, fixture.decimalPreperiod + fixture.decimalPeriod);
    assert.equal(decimalEnd.wordIndex, fixture.decimalIndex);
    assert.equal(decimalEnd.power, fixture.multiplier ** BigInt(fixture.decimalIndex));
    assert.equal(decimalEnd.wordText, fixture.decimalWord);
    assert.equal(decimalEnd.split, fixture.split);
    assert.equal(decimalEnd.endingPart + decimalEnd.followingPart, fixture.decimalWord);
    assert.equal(decimalEnd.coefficientCount, fixture.decimalIndex + 1);
    assert.equal(decimalEnd.remainderBefore, fixture.decimalBefore);
    assert.equal(decimalEnd.remainderAfter, fixture.decimalAfter);
    assert.equal(decimalEnd.remainderAfter, model.decimal.repeatRemainder);

    assert.equal(groupedEnd.wordIndex, fixture.groupedIndex);
    assert.equal(groupedEnd.power, fixture.multiplier ** BigInt(fixture.groupedIndex));
    assert.equal(groupedEnd.wordText, fixture.groupedWord);
    assert.equal(groupedEnd.coefficientCount, fixture.groupedIndex + 1);
    assert.equal(groupedEnd.coefficientCount, model.grouped.preperiod + model.grouped.period);
    assert.equal(groupedEnd.remainderBefore, fixture.groupedBefore);
    assert.equal(groupedEnd.remainderAfter, fixture.groupedAfter);
    assert.equal(groupedEnd.remainderAfter, model.grouped.repeatRemainder);
    assert.equal(model.decimal.rows[model.decimal.preperiod]!.remainder, decimalEnd.remainderAfter);
    assert.equal(model.grouped.rows[model.grouped.preperiod]!.remainder, groupedEnd.remainderAfter);
  });

  test(`1/${fixture.denominator}: all words, split boundaries, and repeat witnesses agree with decimal division`, () => {
    const model = REPETITION_BOUNDARIES.find(item => item.denominator === fixture.denominator)!;
    let remainder = 1n;
    let decimalDigits = "";
    const digitCount = 2 * model.grouped.rows.length * model.width + model.width;
    const remainders = [remainder];
    for (let index = 0; index < digitCount; index += 1) {
      const shifted = 10n * remainder;
      decimalDigits += String(shifted / fixture.denominator);
      remainder = shifted % fixture.denominator;
      remainders.push(remainder);
    }

    const seen = new Set<bigint>();
    for (const row of model.decimal.rows) {
      assert(!seen.has(row.remainder), "A shorter remainder cycle must not have been skipped.");
      seen.add(row.remainder);
      assert.equal(10n * row.remainder, row.word * fixture.denominator + row.nextRemainder);
    }
    for (const row of model.grouped.rows) {
      assert.equal(row.word.toString().padStart(model.width, "0"), decimalDigits.slice(row.index * model.width, (row.index + 1) * model.width));
      assert.equal(row.remainder, remainders[row.index * model.width]);
      assert.equal(row.nextRemainder, remainders[(row.index + 1) * model.width]);
      assert.equal(row.remainder, fixture.multiplier ** BigInt(row.index) % fixture.denominator);
    }

    const end = model.decimalEnd.position;
    assert.equal(model.decimalEnd.beforeDigits, decimalDigits.slice(end - 9, end));
    assert.equal(model.decimalEnd.afterDigits, decimalDigits.slice(end, end + 6));
    assert.equal(model.decimalEnd.followingPart, decimalDigits.slice(end, end + model.width - model.decimalEnd.split));
    assert.equal(decimalDigits.slice(model.decimal.preperiod, end), decimalDigits.slice(end, end + model.decimal.period));
    assert.equal(BigInt(model.decimal.cycle) * fixture.denominator,
      10n ** BigInt(model.decimal.preperiod) * (10n ** BigInt(model.decimal.period) - 1n));
  });

  test(`1/${fixture.denominator}: a closed remainder cycle still has an exact nonzero geometric tail`, () => {
    const model = REPETITION_BOUNDARIES.find(item => item.denominator === fixture.denominator)!;
    const count = model.groupedEnd.coefficientCount;
    const trace = recurrenceTrace({ base: model.base, coefficients: [model.multiplier] }, count);
    for (const terms of new Set([model.decimalEnd.coefficientCount, count])) {
      const certificate = certifiedPrefix(trace, terms);
      assert.equal(certificate.stateAfterPrefix, model.multiplier ** BigInt(terms));
      assert(certificate.residual.numerator > 0n);
      assert.equal(certificate.prefix.numerator * fixture.denominator + certificate.residual.numerator,
        certificate.prefix.denominator);
      assert.equal(certificate.boundaryCarry, model.multiplier ** BigInt(terms) / fixture.denominator);
      assert.equal(certificate.settledPrefixInteger, model.base ** BigInt(terms) / fixture.denominator);
      assert.equal(certificate.canonicalRemainder, trace.rows[terms - 1]!.nextRemainder);
    }
  });
}

test("997's decimal repetition returns before the three-digit grouping realigns", () => {
  const model = REPETITION_BOUNDARIES[1]!;
  assert.equal(model.decimalEnd.endingPart, "7");
  assert.equal(model.decimalEnd.followingPart, "00");
  assert.equal(model.grouped.period * model.width, 3 * model.decimal.period);
  assert.equal(model.grouped.rows[model.decimalEnd.wordIndex]!.nextRemainder, 100n);
  assert.notEqual(model.decimalEnd.remainderAfter, model.grouped.rows[model.decimalEnd.wordIndex]!.nextRemainder);
});

test("invalid widths, non-repeating fractions, and constant progressions are rejected", () => {
  assert.throws(() => buildRepetitionBoundary(97n, 0), RangeError);
  assert.throws(() => buildRepetitionBoundary(97n, 2.5), RangeError);
  assert.throws(() => buildRepetitionBoundary(97n, 7), RangeError);
  assert.throws(() => buildRepetitionBoundary(100n, 2), RangeError);
  assert.throws(() => buildRepetitionBoundary(99n, 2), RangeError);
  assert.throws(() => buildRepetitionBoundary(1n, 2), RangeError);
  assert.throws(() => buildRepetitionBoundary(8n, 1), /repeating reciprocal/);
});
