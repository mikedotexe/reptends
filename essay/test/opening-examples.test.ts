import test from "node:test";
import assert from "node:assert/strict";
import { formatWord } from "../src/math/lifts.ts";
import { OPENING_EXAMPLES } from "../src/opening-examples.ts";

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
