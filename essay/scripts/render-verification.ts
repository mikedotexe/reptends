import { formatWord, recurrenceTrace } from "../src/math/lifts.ts";
import { certifiedPrefix } from "../src/math/unfolded-notation.ts";
import { REPETITION_BOUNDARIES } from "../src/repetition-boundaries.ts";
import type { DivisionStep } from "../src/repetition-boundaries.ts";

const repository = "https://github.com/mikedotexe/reptends/blob/main/";
const atlas = `${repository}docs/PROOF_STATUS_ATLAS.md`;
const escapeHtml = (value: string): string => value.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
const stepWitness = (row: DivisionStep) => ({
  remainder_before: String(row.remainder),
  emitted_integer: String(row.word),
  remainder_after: String(row.nextRemainder),
});

/** Build-time evidence only; the browser neither evaluates nor depends on it. */
function verificationCertificate() {
  return {
    schema_version: 1,
    description: "Exact long-division evidence for the four curated endpoint comparisons.",
    conventions: {
      decimal_radix: 10,
      word_index: "Zero-based index i; interface group i + 1 is associated with k^i, beginning with k^0 = 1.",
      remainder: "r_i enters the word at zero-based index i (interface group i + 1); r_0 = 1. A cycle ends on the first repeated remainder.",
      endpoint: "decimal.endpoint.position counts digits including the nonrepeating prefix; grouped.endpoint.word_index includes startup words.",
      split_after: "Number of digits in the containing word through the first decimal endpoint; from 1 through word_width.",
      integer_encoding: "Arithmetic integers are decimal strings; bounded lengths, positions, and schema_version are JSON numbers.",
      evidence_status: "Computed examples with independently reproducible witnesses; not a formal proof certificate.",
    },
    claims: [
      { id: "series_q_weighted_identity", status: "reproved-here", source: atlas },
      { id: "incoming_carry_position_formula", status: "reproved-here", source: atlas },
      { id: "digit_periodicity", status: "reproved-here", scope: "Coprime prime examples", source: atlas },
      { id: "power_order_formula", status: "classical", source: atlas },
      { id: "preperiod_from_base_factors", status: "classical", source: atlas },
    ],
    cases: REPETITION_BOUNDARIES.map(item => {
      const terms = item.grouped.rows.length;
      const trace = recurrenceTrace({ base: item.base, coefficients: [item.multiplier] }, terms);
      const prefix = certifiedPrefix(trace, terms);
      const first = item.firstChangedRow;
      return {
        denominator: String(item.denominator),
        word_width: item.width,
        block_base: String(item.base),
        quotient: "1",
        multiplier: String(item.multiplier),
        decimal: {
          preperiod_length: item.decimal.preperiod,
          period_length: item.decimal.period,
          prefix_digits: item.decimal.prefix,
          period_digits: item.decimal.cycle,
          return_remainder: String(item.decimal.repeatRemainder),
          endpoint: {
            position: item.decimalEnd.position,
            word_index: item.decimalEnd.wordIndex,
            power: String(item.decimalEnd.power),
            containing_word: item.decimalEnd.wordText,
            split_after: item.decimalEnd.split,
            ending_part: item.decimalEnd.endingPart,
            following_part: item.decimalEnd.followingPart,
            final_digit_step: stepWitness(item.decimal.rows.at(-1)!),
          },
        },
        grouped: {
          preperiod_length: item.grouped.preperiod,
          period_length: item.grouped.period,
          prefix_words: item.grouped.rows.slice(0, item.grouped.preperiod).map(row => formatWord(row.word, item.base)),
          period_words: item.grouped.rows.slice(item.grouped.preperiod).map(row => formatWord(row.word, item.base)),
          return_remainder: String(item.grouped.repeatRemainder),
          endpoint: {
            word_index: item.groupedEnd.wordIndex,
            power: String(item.groupedEnd.power),
            word: item.groupedEnd.wordText,
            final_word_step: stepWitness(item.grouped.rows.at(-1)!),
          },
        },
        first_incoming_carry: {
          word_index: item.firstChangedIndex,
          raw_power: String(first.raw),
          next_power: String(first.nextLift),
          incoming_carry: String(first.carryIn),
          previous_boundary_carry: String(first.quotient),
          printed_word: formatWord(first.word, item.base),
          word_step: stepWitness(item.grouped.rows[item.firstChangedIndex]!),
        },
        finite_prefix: {
          terms,
          raw_prefix_integer: String(prefix.prefix.numerator),
          base_power: String(prefix.prefix.denominator),
          remaining_power: String(prefix.stateAfterPrefix),
          boundary_carry: String(prefix.boundaryCarry),
          settled_prefix_integer: String(prefix.settledPrefixInteger),
          remainder: String(prefix.canonicalRemainder),
        },
      };
    }),
  };
}

/** Small, dependency-free independent calculation, not a call into the TS engine. */
function pythonVerifier(): string {
  const fixtures = REPETITION_BOUNDARIES.map(item =>
    `    (${item.denominator}, ${item.width}, ${item.decimal.preperiod}, ${item.decimal.period}, ${item.grouped.preperiod}, ${item.grouped.period}, ${item.firstChangedIndex}, ${item.decimalEnd.wordIndex}, ${item.decimalEnd.split}, "${item.decimalEnd.wordText}", ${item.groupedEnd.wordIndex}, "${item.groupedEnd.wordText}"),`,
  ).join("\n");
  return `# Python 3; standard library only. All division is exact integer division.
# Each fixture: D, width, decimal prefix/period, word prefix/period,
# first carry index, decimal-end word index/split/word, final word index/word.
CASES = [
${fixtures}
]

def divide(D, B):
    seen, words, states = {}, [], []
    r = 1
    while r not in seen:
        assert r != 0, "These four examples must repeat."
        seen[r] = len(words)
        states.append(r)
        word, r = divmod(B * r, D)
        words.append(word)
    start = seen[r]
    return start, len(words) - start, words, states, r

for D, width, dm, dl, wm, wl, first, end, split, word, last, final in CASES:
    B = 10 ** width
    k = B - D
    assert 2 <= k < D and B == D + k
    dec = divide(D, 10)
    grp = divide(D, B)
    assert dec[:2] == (dm, dl) and grp[:2] == (wm, wl)
    assert (end, split) == ((dm + dl - 1) // width, (dm + dl - 1) % width + 1)
    assert str(grp[2][end]).zfill(width) == word
    assert last == wm + wl - 1 and str(grp[2][last]).zfill(width) == final
    assert dec[4] == dec[3][dm] and grp[4] == grp[3][wm]
    assert k ** first < D <= k ** (first + 1)
    assert next(i for i, v in enumerate(grp[2]) if v != k ** i) == first

    # Check every emitted word in a complete transient + cycle.
    A = 0
    for i, (r, printed) in enumerate(zip(grp[3], grp[2])):
        power = k ** i
        local_digit, next_r = divmod(k * r, D)
        Q, expected_r = divmod(power, D)
        C = (k * power) // D
        assert r == expected_r
        assert printed == power + C - B * Q == r + local_digit
        assert B * r == D * printed + next_r
        A = B * A + power
        m = i + 1
        assert D * A + k ** m == B ** m
        assert A + k ** m // D == B ** m // D
    print(f"1/{D}: decimal {dm}+{dl}; words {wm}+{wl}; "
          f"first carry {k}^{first}; endpoints {k}^{end} / {k}^{last}; verified")

print("All four cases verified, including minimal remainder cycles and finite prefixes.")`;
}

export function renderVerificationCertificate(): string {
  const json = JSON.stringify(verificationCertificate(), null, 2).replace(/</g, "\\u003c");
  return `<script type="application/json" id="reptends-certificate">\n${json}\n</script>`;
}

export function renderVerificationGuide(): string {
  const receipts = REPETITION_BOUNDARIES.map(item => {
    const digit = item.decimal.rows.at(-1)!;
    const word = item.grouped.rows.at(-1)!;
    return `<tr><th scope="row">1/${item.denominator}</th><td>${item.decimal.preperiod} + ${item.decimal.period}</td><td>${item.grouped.preperiod} + ${item.grouped.period}</td><td>10 × ${digit.remainder} = ${item.denominator} × ${digit.word} + ${digit.nextRemainder}<br>${item.base} × ${word.remainder} = ${item.denominator} × ${word.word} + ${word.nextRemainder}</td></tr>`;
  }).join("\n");
  return `<details id="verification-guide" class="research-detail"><summary>Verify the four examples, by hand or with code</summary>
    <div class="prose">
      <p>These four examples use classical division and geometric series. The <a href="${atlas}">proof-status atlas</a> records the scope of the underlying results; detailed statuses follow the independent verifier.</p>
      <h3>Assumptions and indexing</h3>
      <p>For these examples, B = 10<sup>w</sup>, D = B − k, and 2 ≤ k &lt; D. The quotient in B = qD + k is q = 1. The tuples (D, w, B, q, k) are (97, 2, 100, 1, 3), (997, 3, 1000, 1, 3), (94, 2, 100, 1, 6), and (994, 3, 1000, 1, 6). Because k/B &lt; 1, their geometric series converge. The mathematical index i begins at 0; the interface labels that position “group i + 1.” It corresponds to k<sup>i</sup>. Remainder r<sub>i</sub> is the state <em>before</em> that word, with r<sub>0</sub> = 1.</p>
      <h3>Two kinds of quotient</h3>
      <p>Write k<sup>i</sup> = DQ<sub>i</sub> + r<sub>i</sub>, where Q<sub>i</sub> = floor(k<sup>i</sup>/D) and 0 ≤ r<sub>i</sub> &lt; D. The incoming boundary carry is C<sub>i</sub> = Q<sub>i+1</sub>. Substituting B = D + k into ordinary division gives:</p>
      <p class="formula">Brᵢ = DWᵢ + rᵢ₊₁<br>Wᵢ = kⁱ + Qᵢ₊₁ − BQᵢ = kⁱ + Cᵢ − BCᵢ₋₁</p>
      <p>Here C<sub>−1</sub> = Q<sub>0</sub> = 0. By contrast, the local quotient digit d<sub>i</sub> = floor(kr<sub>i</sub>/D) is bounded: 0 ≤ d<sub>i</sub> &lt; k. It gives kr<sub>i</sub> = Dd<sub>i</sub> + r<sub>i+1</sub> and W<sub>i</sub> = r<sub>i</sub> + d<sub>i</sub>. This local digit and the potentially huge boundary carry are different quantities. The first incoming carry occurs at the least i with k<sup>i+1</sup> ≥ D.</p>
      <h3>The exact balance after a finite prefix</h3>
      <p>For m ≥ 0, let A<sub>m</sub> = Σ<sub>j=0</sub><sup>m−1</sup> k<sup>j</sup>B<sup>m−1−j</sup>, with A<sub>0</sub> = 0. Multiplying by D = B − k makes consecutive terms cancel:</p>
      <p class="formula">DAₘ + kᵐ = Bᵐ<br>1/D = Aₘ/Bᵐ + kᵐ/(DBᵐ)<br>floor(Bᵐ/D) = Aₘ + floor(kᵐ/D)</p>
      <p>The first line is a finite integer identity. The last line settles the first m words exactly; the remainder is k<sup>m</sup> mod D. Thus the final displayed power is a position marker, while the remaining terms still have an exact balance. This specializes the <a href="${repository}essay/src/math/unfolded-notation.ts">general finite-prefix certificate in the arithmetic engine</a>.</p>
      <h3>Returning-state witnesses</h3>
      <p>Each length below is “startup + minimal repeating cycle.” The decimal and word columns use different step sizes. For 94 and 994, the returning state is reached after startup; it is not the original remainder 1. A returning state proves repetition; checking that no state repeated earlier proves minimality.</p>
      <div class="boundary-table-scroll" tabindex="0" role="region" aria-label="Exact cycle lengths and returning remainder equations; horizontally scrollable"><table class="boundary-table"><caption>Independent long-division checks</caption><thead><tr><th scope="col">Fraction</th><th scope="col">Decimal digits</th><th scope="col">Grouped words</th><th scope="col">Final digit and word equations</th></tr></thead><tbody>${receipts}</tbody></table></div>
      <h3>Recompute it independently</h3>
      <p>Copy this into a file and run it with Python 3. It uses only integers and the standard library. It detects the first repeated remainder in each radix, checks every word through the first complete cycle, and verifies the carry and finite-prefix identities at every position. It imports none of this website’s arithmetic.</p>
      <pre class="verification-code" tabindex="0" aria-label="Copyable Python 3 verification program"><code>${escapeHtml(pythonVerifier())}</code></pre>
      <p>The <a href="${atlas}">proof-status atlas</a> records <code>series_q_weighted_identity</code> and <code>incoming_carry_position_formula</code> as <strong>reproved-here</strong>, <code>digit_periodicity</code> as <strong>reproved-here</strong> for coprime prime denominators, and <code>power_order_formula</code> and <code>preperiod_from_base_factors</code> as <strong>classical</strong>. The four examples below are exact computations. The algebra connecting their displays is shown here; it has no separate formal claim ID.</p>
      <p>For machines, this HTML also contains a non-executable JSON record in <code>script#reptends-certificate</code>, schema version 1: all four complete decimal and grouped cycles, endpoint equations, first-carry witnesses, and an exact finite-prefix balance. Arithmetic integers are decimal strings; lengths and indices are numbers. These reproducible checks support the implementation. They do not certify the full recurrence framework in a proof assistant.</p>
    </div>
  </details>`;
}
