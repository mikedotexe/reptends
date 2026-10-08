import test from "node:test";
import assert from "node:assert/strict";
import { formatWord } from "../src/math/lifts.ts";
import {
  OPENING_EXAMPLES,
  POWER_STACK,
  POWER_STACK_RESULT,
  STACK_FIRST_GROUP,
  STACK_LAST_GROUP,
  STACK_RESULT_LAST_GROUP,
} from "../src/opening-examples.ts";

const expected = [
  {
    denominator: 97n,
    width: 2,
    firstChangedIndex: 4,
    raw: 81n,
    word: 83n,
    groups: "01 03 09 27 83 50 51 54 63 91 75 25 77 31 95 87",
  },
  {
    denominator: 997n,
    width: 3,
    firstChangedIndex: 6,
    raw: 729n,
    word: 731n,
    groups: "001 003 009 027 081 243 731 193 580 742 226 680 040 120 361 083",
  },
  {
    denominator: 9997n,
    width: 4,
    firstChangedIndex: 8,
    raw: 6561n,
    word: 6562n,
    groups: "0001 0003 0009 0027 0081 0243 0729 2187 6562 9688 9066 7200 1600 4801 4404 3212",
  },
] as const;

test("the opening compares denominators three below successive powers of ten", () => {
  assert.deepEqual(OPENING_EXAMPLES.map(example => example.denominator), [97n, 997n, 9997n]);
  for (const example of OPENING_EXAMPLES) {
    assert.equal(example.base, 10n ** BigInt(example.width));
    assert.equal(example.denominator, example.base - 3n);
  }
});

for (const fixture of expected) {
  test("opening 1/" + fixture.denominator + " preserves every decimal digit and its first correction", () => {
    const example = OPENING_EXAMPLES.find(item => item.denominator === fixture.denominator)!;
    assert(example);
    assert.equal(example.width, fixture.width);
    assert.equal(example.rows.length, 16);

    // This oracle emits one decimal digit at a time. It does not use the
    // recurrence, grouped-word base, lifted states, or carry coordinates.
    let remainder = 1n;
    let decimalDigits = "";
    for (let position = 0; position < 16 * fixture.width; position += 1) {
      const shifted = 10n * remainder;
      decimalDigits += String(shifted / fixture.denominator);
      remainder = shifted % fixture.denominator;
    }

    const groups = example.rows.map(row => formatWord(row.word, example.base));
    assert.equal(groups.join(""), decimalDigits);
    assert.equal(groups.join(" "), fixture.groups);
    assert(groups.every(group => group.length === fixture.width));
    assert.equal(groups[0], "0".repeat(fixture.width - 1) + "1");
    assert.equal(example.firstChangedIndex, fixture.firstChangedIndex);

    example.rows.forEach((row, index) => {
      assert.equal(row.raw, 3n ** BigInt(index));
      if (index < fixture.firstChangedIndex) assert.equal(row.word, row.raw);
    });
    const firstChange = example.rows[example.firstChangedIndex]!;
    assert.equal(firstChange.raw, fixture.raw);
    assert.equal(firstChange.word, fixture.word);
    assert(firstChange.raw < example.base, "The correction arrives before this raw term overflows its group.");
  });
}

test("the opening names the final exact power before every first correction", () => {
  assert.deepEqual(OPENING_EXAMPLES.map(example => {
    const last = example.rows[example.firstChangedIndex - 1]!;
    const changed = example.rows[example.firstChangedIndex]!;
    return {
      denominator: example.denominator,
      cleanGroups: example.firstChangedIndex,
      lastPower: last.raw,
      lastExponent: example.firstChangedIndex - 1,
      expectedNext: changed.raw,
      printedNext: changed.word,
    };
  }), [
    { denominator: 97n, cleanGroups: 4, lastPower: 27n, lastExponent: 3, expectedNext: 81n, printedNext: 83n },
    { denominator: 997n, cleanGroups: 6, lastPower: 243n, lastExponent: 5, expectedNext: 729n, printedNext: 731n },
    { denominator: 9997n, cleanGroups: 8, lastPower: 2187n, lastExponent: 7, expectedNext: 6561n, printedNext: 6562n },
  ]);
});

test("full-width powers add column by column to the first number-salad groups", () => {
  assert.equal(STACK_FIRST_GROUP, 5);
  assert.equal(STACK_RESULT_LAST_GROUP, 11);
  assert.equal(STACK_LAST_GROUP, 12);

  for (const row of POWER_STACK) {
    const occupied = row.cells.flatMap((cell, index) => cell === null
      ? []
      : [{ group: STACK_FIRST_GROUP + index, word: cell }]);
    assert(occupied.length > 0);
    assert.equal(occupied[0]!.group, row.firstOccupiedGroup);
    assert.equal(occupied.at(-1)!.group, row.exponent + 1);
    const reconstructed = occupied.reduce((value, cell) => value * 1000n + cell.word, 0n);
    assert.equal(reconstructed, row.power);
  }

  const columnSums = POWER_STACK_RESULT.map((_, index) => POWER_STACK.reduce(
    (sum, row) => sum + (row.cells[index] ?? 0n),
    0n,
  ));
  assert.deepEqual(columnSums, POWER_STACK_RESULT);
  assert.deepEqual(POWER_STACK_RESULT, [81n, 243n, 731n, 193n, 580n, 742n, 226n]);
  assert.deepEqual(columnSums.slice(2), [729n + 2n, 187n + 6n, 561n + 19n, 683n + 59n, 49n + 177n]);
});

test("the shown fractional part plus the entire omitted tail cannot carry into group 11", () => {
  const base = 1000n;
  const denominator = 997n;
  const terms = POWER_STACK.at(-1)!.exponent + 1;
  let rawPrefix = 0n;
  for (let index = 0; index < terms; index += 1) rawPrefix = base * rawPrefix + 3n ** BigInt(index);
  const shownFractionNumerator = rawPrefix % base;
  const remainingPower = 3n ** BigInt(terms);
  // Both unfinished pieces expressed in group-11 units, with a common denominator.
  const unfinishedNumerator = denominator * shownFractionNumerator + remainingPower;
  const unfinishedDenominator = denominator * base;
  assert.equal(shownFractionNumerator, 147n);
  assert.equal(remainingPower, 531441n);
  assert.equal(unfinishedNumerator, 678000n);
  assert(unfinishedNumerator < unfinishedDenominator);
  assert.equal(rawPrefix / base, base ** BigInt(terms - 1) / denominator);
});
