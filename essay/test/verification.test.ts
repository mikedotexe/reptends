import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { renderVerificationCertificate, renderVerificationGuide } from "../scripts/render-verification.ts";

interface StepWitness {
  remainder_before: string;
  emitted_integer: string;
  remainder_after: string;
}
interface CaseCertificate {
  denominator: string;
  word_width: number;
  block_base: string;
  quotient: string;
  multiplier: string;
  decimal: {
    preperiod_length: number;
    period_length: number;
    prefix_digits: string;
    period_digits: string;
    return_remainder: string;
    endpoint: {
      position: number;
      word_index: number;
      power: string;
      containing_word: string;
      split_after: number;
      ending_part: string;
      following_part: string;
      final_digit_step: StepWitness;
    };
  };
  grouped: {
    preperiod_length: number;
    period_length: number;
    prefix_words: string[];
    period_words: string[];
    return_remainder: string;
    endpoint: { word_index: number; power: string; word: string; final_word_step: StepWitness };
  };
  first_incoming_carry: {
    word_index: number;
    raw_power: string;
    next_power: string;
    incoming_carry: string;
    previous_boundary_carry: string;
    printed_word: string;
    word_step: StepWitness;
  };
  finite_prefix: {
    terms: number;
    raw_prefix_integer: string;
    base_power: string;
    remaining_power: string;
    boundary_carry: string;
    settled_prefix_integer: string;
    remainder: string;
  };
}

function readCertificate(): { schema_version: number; cases: CaseCertificate[] } {
  const match = /^<script type="application\/json" id="reptends-certificate">\n([\s\S]+)\n<\/script>$/.exec(renderVerificationCertificate());
  assert(match, "The artifact must have one identifiable, non-executable JSON script.");
  return JSON.parse(match[1]!);
}

/** Independent Euclidean division: no recurrence, boundary model, or period input. */
function longDivision(denominator: bigint, base: bigint) {
  const remainders: bigint[] = [];
  const words: bigint[] = [];
  let remainder = 1n;
  while (!remainders.includes(remainder)) {
    assert(remainder > 0n);
    remainders.push(remainder);
    words.push(base * remainder / denominator);
    remainder = base * remainder % denominator;
    assert(words.length <= Number(denominator), "Finite remainder states must repeat.");
  }
  const preperiod = remainders.indexOf(remainder);
  return { remainders, words, preperiod, period: words.length - preperiod, returned: remainder };
}

function assertStep(step: StepWitness, denominator: bigint, base: bigint, before: bigint, word: bigint, after: bigint) {
  assert.deepEqual(step, { remainder_before: String(before), emitted_integer: String(word), remainder_after: String(after) });
  assert.equal(base * before, denominator * word + after);
  assert(after >= 0n && after < denominator);
}

const expected = [
  ["97", 2, 0, 96, 0, 48, 4, 47, 2, "67", 47, "67"],
  ["997", 3, 0, 166, 0, 166, 6, 55, 1, "700", 165, "667"],
  ["94", 2, 1, 46, 1, 23, 2, 23, 1, "51", 23, "51"],
  ["994", 3, 1, 210, 1, 70, 3, 70, 1, "501", 70, "501"],
] as const;

test("the evidence schema identifies every curated tuple and the three distinct endpoints", () => {
  const certificate = readCertificate();
  assert.equal(certificate.schema_version, 1);
  assert.equal(certificate.cases.length, 4);
  assert.deepEqual(certificate.cases.map(item => [
    item.denominator, item.word_width,
    item.decimal.preperiod_length, item.decimal.period_length,
    item.grouped.preperiod_length, item.grouped.period_length,
    item.first_incoming_carry.word_index,
    item.decimal.endpoint.word_index, item.decimal.endpoint.split_after, item.decimal.endpoint.containing_word,
    item.grouped.endpoint.word_index, item.grouped.endpoint.word,
  ]), expected);
});

for (const [denominator] of expected) {
  test(`1/${denominator}: certificate cycles, endpoint equations, and exact balance agree with independent division`, () => {
    const item = readCertificate().cases.find(value => value.denominator === denominator)!;
    const D = BigInt(item.denominator);
    const B = 10n ** BigInt(item.word_width);
    const k = B - D;
    assert.equal(item.block_base, String(B));
    assert.equal(item.multiplier, String(k));
    assert.equal(item.quotient, "1");
    assert(2n <= k && k < D);
    const dec = longDivision(D, 10n);
    const grp = longDivision(D, B);
    const decimalDigits = dec.words.join("");
    const groupedWords = grp.words.map(word => String(word).padStart(item.word_width, "0"));
    assert.equal(item.decimal.preperiod_length, dec.preperiod);
    assert.equal(item.decimal.period_length, dec.period);
    assert.equal(item.decimal.prefix_digits, decimalDigits.slice(0, dec.preperiod));
    assert.equal(item.decimal.period_digits, decimalDigits.slice(dec.preperiod));
    assert.equal(item.decimal.return_remainder, String(dec.returned));
    assert.equal(item.grouped.preperiod_length, grp.preperiod);
    assert.equal(item.grouped.period_length, grp.period);
    assert.deepEqual(item.grouped.prefix_words, groupedWords.slice(0, grp.preperiod));
    assert.deepEqual(item.grouped.period_words, groupedWords.slice(grp.preperiod));
    assert.equal(item.grouped.return_remainder, String(grp.returned));

    const end = item.decimal.endpoint;
    assert.equal(end.position, dec.words.length);
    assert.equal(end.word_index, Math.floor((end.position - 1) / item.word_width));
    assert.equal(end.split_after, (end.position - 1) % item.word_width + 1);
    assert.equal(end.power, String(k ** BigInt(end.word_index)));
    assert.equal(end.containing_word, groupedWords[end.word_index]);
    assert.equal(end.ending_part, end.containing_word.slice(0, end.split_after));
    assert.equal(end.following_part, end.containing_word.slice(end.split_after));
    assertStep(end.final_digit_step, D, 10n, dec.remainders.at(-1)!, dec.words.at(-1)!, dec.returned);
    const last = item.grouped.endpoint;
    assert.equal(last.word_index, grp.words.length - 1);
    assert.equal(last.power, String(k ** BigInt(last.word_index)));
    assert.equal(last.word, groupedWords.at(-1));
    assertStep(last.final_word_step, D, B, grp.remainders.at(-1)!, grp.words.at(-1)!, grp.returned);

    const first = item.first_incoming_carry;
    const i = first.word_index;
    const raw = k ** BigInt(i);
    assert(raw < D && raw * k >= D, "The first incoming carry must be the earliest crossing.");
    assert.equal(first.raw_power, String(raw));
    assert.equal(first.next_power, String(raw * k));
    assert.equal(first.incoming_carry, String(raw * k / D));
    assert.equal(first.previous_boundary_carry, "0");
    assert.equal(first.printed_word, groupedWords[i]);
    assert.equal(grp.words.findIndex((word, index) => word !== k ** BigInt(index)), i);
    assertStep(first.word_step, D, B, grp.remainders[i]!, grp.words[i]!, grp.remainders[i + 1]!);

    const prefix = item.finite_prefix;
    assert.equal(prefix.terms, grp.words.length);
    const m = BigInt(prefix.terms);
    const A = grp.words.reduce((sum, _, index) => B * sum + k ** BigInt(index), 0n);
    const settled = grp.words.reduce((sum, word) => B * sum + word, 0n);
    assert.equal(prefix.raw_prefix_integer, String(A));
    assert.equal(prefix.base_power, String(B ** m));
    assert.equal(prefix.remaining_power, String(k ** m));
    assert.equal(prefix.boundary_carry, String(k ** m / D));
    assert.equal(prefix.settled_prefix_integer, String(settled));
    assert.equal(prefix.remainder, String(grp.returned));
    assert.equal(D * A + k ** m, B ** m);
    assert.equal(A + k ** m / D, settled);
    assert.equal(D * settled + grp.returned, B ** m);
  });
}

test("the human-readable verifier runs independently and recomputes every displayed fixture", t => {
  const guide = renderVerificationGuide();
  const match = /<pre class="verification-code"[^>]*><code>([\s\S]*?)<\/code><\/pre>/.exec(guide);
  assert(match);
  const program = match[1]!.replace(/&quot;/g, '"').replace(/&gt;/g, ">").replace(/&lt;/g, "<").replace(/&amp;/g, "&");
  const result = spawnSync("python3", ["-c", program], { encoding: "utf8", timeout: 10_000 });
  if (result.error && "code" in result.error && result.error.code === "ENOENT") {
    t.skip("Python 3 is not installed; the independent Node checks remain mandatory.");
    return;
  }
  assert.equal(result.error, undefined);
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stderr, "");
  assert.equal(result.stdout, [
    "1/97: decimal 0+96; words 0+48; first carry 3^4; endpoints 3^47 / 3^47; verified",
    "1/997: decimal 0+166; words 0+166; first carry 3^6; endpoints 3^55 / 3^165; verified",
    "1/94: decimal 1+46; words 1+23; first carry 6^2; endpoints 6^23 / 6^23; verified",
    "1/994: decimal 1+210; words 1+70; first carry 6^3; endpoints 6^70 / 6^70; verified",
    "All four cases verified, including minimal remainder cycles and finite prefixes.", "",
  ].join("\n"));
});
