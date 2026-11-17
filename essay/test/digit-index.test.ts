import test from "node:test";
import assert from "node:assert/strict";
import {
  MAX_RANGE, MAX_CHECK_POSITION, parseWhole, modPow, remainderBefore,
  digitAt, digitWindow, checkByLongDivision, formatDigit,
} from "../src/math/digit-index.ts";

/** Independent oracle records the finite remainder machine by walking it. */
function orbit(numerator: bigint, denominator: bigint, radix: bigint) {
  const remainders: bigint[] = [];
  const digits: bigint[] = [];
  const seen = new Map<bigint, number>();
  let r = numerator % denominator;
  while (!seen.has(r)) {
    seen.set(r, remainders.length);
    remainders.push(r);
    digits.push(radix * r / denominator);
    r = radix * r % denominator;
  }
  const lead = seen.get(r)!;
  const period = remainders.length - lead;
  const offset = (position: bigint) => {
    const index = position - 1n;
    return index < BigInt(remainders.length) ? Number(index)
      : lead + Number((index - BigInt(lead)) % BigInt(period));
  };
  return { at: (position: bigint) => ({ remainder: remainders[offset(position)]!, digit: digits[offset(position)]! }), lead, period };
}

test("bounded integer parsing accepts grouped values and exact exponent notation", () => {
  for (const [input, expected] of [
    ["997", 997n], [" 1,000_000 ", 1000000n], ["00000007", 7n],
    ["10^100", 10n ** 100n], ["10**100", 10n ** 100n],
    ["3e9", 3000000000n], ["3E9", 3000000000n],
    ["0^0", 1n], ["0^4096", 0n], ["1^4096", 1n], ["0e4096", 0n],
  ] as const) assert.equal(parseWhole(input, "Value", 256), expected);
  assert.equal(parseWhole("2^850", "Position", 256), 2n ** 850n);
  assert.equal(parseWhole("1e255", "Position", 256), 10n ** 255n);
  assert.equal(parseWhole("1000^85", "Position", 256), 1000n ** 85n);
  assert.equal(parseWhole("9", "Value", 1), 9n);
  assert.equal(parseWhole("9e0", "Value", 1), 9n);
});

test("parsing bounds raw input, exponent size and intermediate products before large allocations", () => {
  for (const input of ["", "-1", "+1", "1.5", "Infinity", "10^-1", "1e-2", "1e1.5", "0x10", "x", "1/7"]) {
    assert.throws(() => parseWhole(input, "Value"), /whole number/);
  }
  assert.throws(() => parseWhole("0".repeat(10000), "Value"), /too long/);
  assert.throws(() => parseWhole("9".repeat(129), "Value"), /128 digits/);
  assert.throws(() => parseWhole("2^851", "Position", 256), /256 digits/);
  assert.throws(() => parseWhole("1e256", "Position", 256), /256 digits/);
  assert.throws(() => parseWhole("999999^4096", "Value"), /128 digits/);
  assert.throws(() => parseWhole("0^999999999999999999999", "Value"), /exponent/);
  assert.throws(() => parseWhole("1e4097", "Value"), /exponent/);
  for (const limit of [0, -1, 1.5, NaN, Infinity, 1025]) assert.throws(() => parseWhole("1", "Value", limit), RangeError);
});

test("modular powers agree with literal integer powers on a bounded independent domain", () => {
  for (let B = 0n; B <= 20n; B++) {
    for (let D = 1n; D <= 30n; D++) {
      for (let exponent = 0n; exponent <= 12n; exponent++) {
        assert.equal(modPow(B, exponent, D), B ** exponent % D);
      }
    }
  }
  for (const [B, exponent, D] of [[-1n, 2n, 7n], [2n, -1n, 7n], [2n, 2n, 0n]] as const) {
    assert.throws(() => modPow(B, exponent, D), RangeError);
  }
});

test("indexed digits and windows agree with successive long division across bases and improper fractions", () => {
  let checked = 0;
  for (const B of [2n, 3n, 8n, 10n, 16n, 37n, 1000n]) {
    for (let D = 1n; D <= 24n; D++) {
      for (let A = 0n; A <= D + 2n; A++) {
        let r = A % D;
        const expected: bigint[] = [];
        const incoming: bigint[] = [];
        for (let position = 1n; position <= 24n; position++) {
          incoming.push(r);
          const scaled = B * r;
          const digit = scaled / D;
          assert.equal(remainderBefore(A, D, B, position), r);
          assert.equal(digitAt(A, D, B, position), digit);
          expected.push(digit);
          r = scaled % D;
          checked++;
        }
        const window = digitWindow({ numerator: A, denominator: D, radix: B, start: 7n, count: 18 });
        assert.deepEqual(window.digits, expected.slice(6));
        assert.equal(window.remainderBefore, incoming[6]);
        assert.equal(window.remainderAfter, r);
        assert.equal(window.integerPart, A / D);
        assert(Object.isFrozen(window));
        assert(Object.isFrozen(window.digits));
      }
    }
  }
  assert.equal(checked, 62496);
});

test("huge indices agree with independently discovered finite remainder orbits", () => {
  const giant = 10n ** 100n;
  for (const [A, D, B] of [
    [1n, 997n, 10n], [1n, 997n, 1000n], [1n, 9899n, 10n],
    [3n, 7n, 10n], [22n, 7n, 16n], [1n, 12n, 10n],
    [1n, 8n, 10n], [14n, 7n, 2n], [0n, 1n, 1000n],
  ] as const) {
    const reference = orbit(A, D, B);
    const row = digitWindow({ numerator: A, denominator: D, radix: B, start: giant, count: 9 });
    assert.equal(row.remainderBefore, reference.at(giant).remainder);
    for (let j = 0; j < row.count; j++) assert.equal(row.digits[j], reference.at(giant + BigInt(j)).digit);
  }
  assert.equal(digitAt(1n, 997n, 1000n, 1000000n), 83n);
  assert.equal(digitAt(1n, 997n, 1000n, giant), 10n);
  assert.equal(digitAt(1n, 997n, 1000n, 167n), 1n);
  assert.equal(digitAt(1n, 997n, 1000n, 168n), 3n);
  assert.equal(digitAt(1n, 7n, 10n, 1000000000n), 8n);
});

test("formatting preserves digit boundaries in nondecimal bases", () => {
  assert.equal(formatDigit(0n, 10n), "0");
  assert.equal(formatDigit(9n, 10n), "9");
  assert.equal(formatDigit(15n, 16n), "F");
  assert.equal(formatDigit(35n, 36n), "Z");
  assert.equal(formatDigit(1n, 1000n), "001");
  assert.equal(formatDigit(731n, 1000n), "731");
  assert.equal(formatDigit(36n, 37n), "[36]");
  assert.equal(formatDigit(100n, 256n), "[100]");
  for (const [digit, B] of [[-1n, 10n], [10n, 10n], [0n, 1n]] as const) assert.throws(() => formatDigit(digit, B), RangeError);
});

test("window validation rejects invalid domains and unbounded output ranges", () => {
  const spec = { numerator: 1n, denominator: 997n, radix: 10n, start: 1n, count: 10 };
  for (const changes of [
    { numerator: -1n }, { denominator: 0n }, { radix: 1n }, { start: 0n },
    { count: 0 }, { count: MAX_RANGE + 1 }, { count: NaN }, { count: 0.5 },
  ]) assert.throws(() => digitWindow({ ...spec, ...changes }), RangeError);
  assert.equal(digitWindow({ ...spec, count: MAX_RANGE }).digits.length, MAX_RANGE);
});

test("sequential checks walk from the beginning and independently compare the complete window", async () => {
  for (const spec of [
    { numerator: 1n, denominator: 997n, radix: 1000n, start: 167n, count: 20 },
    { numerator: 22n, denominator: 7n, radix: 16n, start: 99n, count: 15 },
    { numerator: 1n, denominator: 8n, radix: 10n, start: 1001n, count: 10 },
    { numerator: 0n, denominator: 1n, radix: 2n, start: 1n, count: 10 },
  ]) {
    const window = digitWindow(spec);
    const result = await checkByLongDivision(window, { yieldControl: async () => {} });
    assert.deepEqual(result, { status: "matched", steps: spec.start + BigInt(spec.count) - 1n });
  }
  const window = digitWindow({ numerator: 1n, denominator: 997n, radix: 10n, start: 50001n, count: 10 });
  const progress: bigint[] = [];
  let yielded = 0;
  const result = await checkByLongDivision(window, {
    onProgress: completed => progress.push(completed),
    yieldControl: async () => { yielded++; },
  });
  assert.equal(result.status, "matched");
  assert.equal(result.steps, 50010n);
  assert.equal(yielded, 50);
  assert.equal(progress.at(-1), 50010n);
  for (let i = 0; i < progress.length; i++) assert(progress[i]! - (progress[i - 1] ?? 0n) <= 1000n);
});

test("independent checking reports wrong digits and either boundary remainder", async () => {
  const window = digitWindow({ numerator: 1n, denominator: 7n, radix: 10n, start: 7n, count: 6 });
  const digits = [...window.digits];
  digits[2] = (digits[2]! + 1n) % 10n;
  assert.deepEqual(await checkByLongDivision({ ...window, digits }), { status: "mismatch", steps: 9n, mismatchPosition: 9n });
  assert.deepEqual(await checkByLongDivision({ ...window, remainderBefore: 0n }), { status: "mismatch", steps: 6n, mismatchPosition: 7n });
  assert.deepEqual(await checkByLongDivision({ ...window, remainderAfter: 0n }), { status: "mismatch", steps: 12n, mismatchPosition: 12n });
});

test("sequential checking cancels before work and around asynchronous yields", async () => {
  const window = digitWindow({ numerator: 1n, denominator: 7n, radix: 10n, start: 9999n, count: 2 });
  const before = new AbortController();
  before.abort();
  assert.deepEqual(await checkByLongDivision(window, { signal: before.signal }), { status: "cancelled", steps: 0n });
  const during = new AbortController();
  let yields = 0;
  const result = await checkByLongDivision(window, {
    signal: during.signal,
    yieldControl: async () => { yields++; during.abort(); },
  });
  assert.deepEqual(result, { status: "cancelled", steps: 1000n });
  assert.equal(yields, 1);
  const onProgress = new AbortController();
  let shouldNotYield = false;
  assert.deepEqual(await checkByLongDivision(window, {
    signal: onProgress.signal,
    onProgress: () => onProgress.abort(),
    yieldControl: async () => { shouldNotYield = true; },
  }), { status: "cancelled", steps: 1000n });
  assert.equal(shouldNotYield, false);
});

test("the walk limit is explicit and checked before sequential work", async () => {
  const beyond = digitWindow({ numerator: 1n, denominator: 7n, radix: 10n, start: MAX_CHECK_POSITION, count: 2 });
  await assert.rejects(checkByLongDivision(beyond), /sequential check stops/);
  await assert.rejects(checkByLongDivision({ ...beyond, count: 1 }), /invalid digit count/);
  const edge = digitWindow({ numerator: 1n, denominator: 8n, radix: 10n, start: MAX_CHECK_POSITION, count: 1 });
  assert.deepEqual(await checkByLongDivision(edge, { yieldControl: async () => {} }), { status: "matched", steps: MAX_CHECK_POSITION });
});
