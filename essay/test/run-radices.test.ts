import test from "node:test";
import assert from "node:assert/strict";
import { advanceRun, decimalTruncation, powerRuns } from "../src/run-radices.ts";
import type { DivisionState } from "../src/run-radices.ts";
import { linkToRun, runFromSearch, positionFromSearch } from "../src/navigation.ts";
import { renderRadixChapter } from "../scripts/render-radices.ts";

test("all 169 power runs agree with direct prefix division and exact tail accounting", () => {
  const rows = powerRuns(997n, 3n, 169);
  let place = 1n;
  for (const [n, row] of rows.entries()) {
    const power = 3n ** BigInt(n);
    place *= 997n * power + 1n;
    assert.equal(row.radix, 997n * power + 1n);
    assert.deepEqual(row.digits, [power]);
    assert.equal(row.after.place, place);
    assert.equal(row.after.quotient, place / 997n);
    assert.equal(row.after.remainder, place % 997n);
    assert.equal(row.after.remainder, 1n);
    assert(row.firstReturn);
    assert(power < row.radix);
    assert.equal(997n * row.after.quotient + 1n, place);
    assert.equal(997n * row.packed, row.radix - 1n);
    assert(row.after.place > row.before.place);
  }
  assert.deepEqual(rows.slice(0, 4).map(r => r.radix), [998n, 2992n, 8974n, 26920n]);
  assert.deepEqual(rows[3]!.after, { place: 721361984161280n, quotient: 723532581907n, remainder: 1n });
});

test("generic power construction is independent of decimal and of the 997 example", () => {
  for (const D of [2n, 7n, 12n, 97n, 997n, 9997n]) {
    for (const c of [2n, 3n, 5n, 12n]) {
      for (const [n, row] of powerRuns(D, c, 12).entries()) {
        assert.equal(row.packed, c ** BigInt(n));
        assert.equal(D * row.after.quotient + row.after.remainder, row.after.place);
        assert.equal(row.after.remainder, 1n);
        assert(row.firstReturn);
      }
    }
  }
});

test("multi-digit runs with radix changes preserve proper fractions including termination", () => {
  for (const [a, D] of [[1n, 997n], [3n, 997n], [5n, 12n], [1n, 8n]] as const) {
    let state: DivisionState = { place: 1n, quotient: 0n, remainder: a };
    for (const run of [{ radix: 10n, length: 4 }, { radix: 30n, length: 7 }, { radix: 2n, length: 11 }, { radix: 1000n, length: 3 }]) {
      const row = advanceRun(D, state, run);
      assert.equal(a * row.after.place, D * row.after.quotient + row.after.remainder);
      assert.equal(row.after.quotient, a * row.after.place / D);
      assert.equal(row.after.remainder, a * row.after.place % D);
      assert.equal(D * row.packed + row.after.remainder, row.scale * state.remainder);
      assert(row.digits.every(d => 0n <= d && d < run.radix));
      state = row.after;
    }
  }
  assert(advanceRun(997n, { place: 1n, quotient: 0n, remainder: 3n }, { radix: 1000n, length: 166 }).firstReturn);
  assert(!advanceRun(997n, { place: 1n, quotient: 0n, remainder: 3n }, { radix: 1000n, length: 332 }).firstReturn);
});

test("decimal views retain actual weights and are explicitly truncated", () => {
  assert.deepEqual(powerRuns(997n, 3n, 4).map(r => decimalTruncation(r.after.quotient, r.after.place)), [
    "0.00100200400801603206", "0.00100300869117914974", "0.00100300902704381314", "0.00100300902708124234",
  ]);
  assert.equal(decimalTruncation(2n, 3n, 2), "0.66");
  assert.equal(decimalTruncation(8n, 3n, 2), "2.66");
});

test("run links coexist with group links and reject ambiguous or invalid positions", () => {
  for (let n = 0; n < 169; n++) {
    const url = new URL(linkToRun(n));
    assert.equal(runFromSearch(url.search), n);
    assert.equal(url.hash, "#change-radix");
  }
  assert.equal(runFromSearch("?group=8&run=167"), 166);
  assert.equal(positionFromSearch("?group=8&run=167"), 7);
  for (const s of ["", "?run=0", "?run=170", "?run=1&run=2", "?run=04", "?run=-1", "?run=1.5", "?run=1e2", "?run=Infinity"]) assert.equal(runFromSearch(s), null);
  for (const n of [-1, 169, 0.5, NaN, Infinity]) assert.throws(() => linkToRun(n), RangeError);
});

test("invalid run inputs are bounded and the static chapter names the changed weights", () => {
  for (const [D, c, n] of [[1n, 3n, 4], [997n, 1n, 4], [997n, 3n, 170]] as const) assert.throws(() => powerRuns(D,c,n), RangeError);
  const state = { place: 1n, quotient: 0n, remainder: 1n };
  for (const run of [{ radix: 1n, length: 1 }, { radix: 10n, length: 0 }, { radix: 10n, length: 1.5 }, { radix: 10n, length: 1001 }]) assert.throws(() => advanceRun(997n,state,run), RangeError);
  const html = renderRadixChapter();
  assert.match(html, /id="change-radix"/);
  assert.match(html, /reproved-here in Lean/);
  assert.match(html, /Changing radices changes the weights/);
  assert.match(html, /positive tail at every finite stage/);
  assert.match(html, /truncated after 20 decimal places/);
});
