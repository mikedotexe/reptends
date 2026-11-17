import assert from "node:assert/strict";
import test from "node:test";
import { continueWithDigit, progressionInfo, progressionRows } from "../src/math/progression.ts";

test("the original base-1000 prefixes match their progression through the handoff", () => {
  for (const example of ["powers", "counting"] as const) {
    const info = progressionInfo(example);
    let remainder = 1n;
    let packed = 0n;
    let power = 1n;
    for (let i = 0; i < info.prefixLength; i++) {
      const digit = remainder * 1000n / info.denominator;
      assert.equal(digit, example === "powers" ? power : BigInt(i));
      remainder = remainder * 1000n % info.denominator;
      packed = packed * 1000n + digit;
      power *= 3n;
    }
    const row = progressionRows(example)[0]!;
    assert.deepEqual(row.before, {
      place: 1000n ** BigInt(info.prefixLength), quotient: packed, remainder,
    });
    assert.equal(remainder, info.initialRemainder);
  }
});

test("997 preserves 729 and continues tripling after its unchanged six groups", () => {
  const rows = progressionRows("powers");
  assert.deepEqual(rows.slice(0, 4).map(r => [r.position, r.desired, r.radix, r.after.remainder]), [
    [7, 729n, 998n, 729n], [8, 2187n, 2992n, 729n],
    [9, 6561n, 8974n, 729n], [10, 19683n, 26920n, 729n],
  ]);
  assert.equal(rows[0]!.ordinaryDigit, 731n);
  assert.equal(rows[0]!.ordinaryRemainder, 193n);
});

test("998001 writes the skipped 998, then 999, 1000, 1001 with their new units", () => {
  const rows = progressionRows("counting");
  assert.deepEqual(rows.slice(0, 4).map(r => [r.position, r.desired, r.radix, r.after.remainder]), [
    [999, 998n, 999n, 999n], [1000, 999n, 998002n, 999n],
    [1001, 1000n, 999001n, 999n], [1002, 1001n, 1000000n, 999n],
  ]);
  assert.equal(rows[0]!.ordinaryDigit, 999n);
  assert.equal(rows[0]!.ordinaryRemainder, 1n);
});

test("every continuation preserves the original fraction and its accumulated weights", () => {
  for (const example of ["powers", "counting"] as const) {
    for (const row of progressionRows(example, 169)) {
      const { denominator: D, desired: d, radix: R, before: old, after: next } = row;
      assert.equal(next.place, old.place * R);
      const prefix = progressionRows(example, 1)[0]!.before;
      assert.equal(next.quotient / (next.place / prefix.place), prefix.quotient);
      assert.equal(next.quotient, old.quotient * R + d);
      assert.equal(D * next.quotient + next.remainder, next.place);
      assert.equal(R * old.remainder, D * d + next.remainder);
      assert(next.remainder > 0n && next.remainder <= old.remainder);
      assert(d < R);
      // The new contribution is exactly the difference between old and new tails.
      assert.equal(D * d, R * old.remainder - next.remainder);
    }
  }
});

test("the rule is legal and locally minimal across denominators and remainders", () => {
  for (let D = 2n; D <= 35n; D++) for (let r = 1n; r < D; r++) {
    for (let d = 1n; d <= 12n; d++) {
      const row = continueWithDigit(D, { place: 1n, quotient: 0n, remainder: r }, d);
      assert.equal(row.packed, d);
      assert(row.radix >= 2n && d < row.radix);
      assert(row.after.remainder > 0n && row.after.remainder <= r);
      // The preceding radix cannot emit d with a positive tail; smaller ones cannot either.
      assert((row.radix - 1n) * r <= D * d);
    }
  }
});

test("a transient return is not mistaken for a permanent fixed remainder", () => {
  let state = { place: 1n, quotient: 0n, remainder: 3n };
  const observed = [];
  for (const d of [1n, 2n, 3n, 4n]) {
    const row = continueWithDigit(7n, state, d);
    observed.push([row.radix, row.after.remainder]);
    state = row.after;
    assert.equal(7n * state.quotient + state.remainder, 3n * state.place);
  }
  assert.deepEqual(observed, [[3n, 2n], [8n, 2n], [11n, 1n], [29n, 1n]]);
});

test("continuation rejects zero tails, nonpositive digits, and invalid bounds", () => {
  for (const [D, r, d] of [[1n, 1n, 1n], [7n, 0n, 1n], [7n, 7n, 1n], [7n, 1n, 0n]]) {
    assert.throws(() => continueWithDigit(D!, { place: 1n, quotient: 0n, remainder: r! }, d!), RangeError);
  }
  for (const count of [0, 170, 1.5, NaN]) assert.throws(() => progressionRows("powers", count), RangeError);
});
