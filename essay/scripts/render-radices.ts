import { decimalTruncation, powerRuns } from "../src/run-radices.ts";
import { progressionRuns, runDigits } from "../src/math/run-notation.ts";
import { renderNotationExamples, renderNotationCertificate } from "./notation-reference.ts";
import { progressionRows } from "../src/math/progression.ts";

const atlas = "https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md";
const proof = "https://github.com/mikedotexe/reptends/blob/main/lean/RadixRuns/Examples.lean";
const handoffProof = "https://github.com/mikedotexe/reptends/blob/main/lean/RadixRuns/BalanceRule.lean";

/** All three worked examples remain readable without JavaScript. */
export function renderRadixChapter(): string {
  const first = powerRuns(997n, 3n, 4);
  const rows = first.map((row, n) => `<tr><th scope="row">${n + 1}</th><td>${row.packed}</td><td>${decimalTruncation(row.after.quotient, row.after.place)}…</td></tr>`).join("");
  const selected = first[3]!;
  const continuation = progressionRows("powers", 8);
  const handoff = continuation[0]!;
  const prefixRun = progressionRuns("powers")[0]!;
  return `<section id="change-radix" class="chapter wrap radix-chapter" aria-labelledby="radix-title" tabindex="-1">
    <div class="chapter-heading"><span class="chapter-number">06 / KEEP THE PROGRESSION VISIBLE</span><h2 id="radix-title">Keep the pattern.<br>Change the units.</h2></div>
    <div class="prose"><p>Back to 1/997. We want to keep writing <strong>729, 2187, 6561</strong>, and every power of three after them. We can keep the first six groups exactly as they are and choose the size of each next place. Another name for that size, or base, is the <strong>radix</strong>. Changing radices changes the weights of later digits; the fraction’s value stays fixed.</p><p>The <a href="${atlas}#unified_balance_rule">proved balance rule</a> turns the remainder into a decision:</p></div>
    <ol class="balance-instructions"><li><strong>Ask for the next progression term.</strong> Multiply the current remainder by the current radix, then subtract 997 times the term we want to write.</li><li><strong>Check what is left.</strong> From 1 through 996, keep the radix and continue. Zero means the fraction is finished.</li><li><strong>If it does not fit, choose a new radix.</strong> Divide 997 times the wanted term by the current remainder. Round down and add 1. This is the smallest radix that writes the term and leaves a positive remainder.</li></ol>
    <div class="balance-first-change"><p>At the first change, the remainder and the wanted term are both 729. Keeping radix 1000 would leave 2187, which is too large.</p><p class="formula">997 × 729 ÷ 729 = 997<br>The next whole number is 998.<br>998 × 729 − 997 × 729 = 729</p><p>Radix <strong>998</strong> writes <strong>729</strong> and leaves <strong>729</strong>. The first six places keep their value. The new digit is worth 729 ÷ (1000⁶ × 998), and each later place includes its own radix in the denominator too.</p></div>
    <div id="notation-guide" class="notation-guide"><h3>One bracket. One radix.</h3>
      <p class="notation-key"><span class="notation-run"><span>⟨1, 3, 9⟩</span><sub>1000</sub></span><span>means three successive digits, each in radix 1000.</span></p>
      <p>Commas separate digits. The subscript gives their radix. A bar <strong>|</strong> marks a radix change; it need not mark a returning remainder. Every digit has weight <strong>1 divided by the product of all radices used through its position</strong>.</p>
      <p class="fine-print">The integers are printed in decimal for readability. The rule and the place values work independently of that display choice.</p>
    </div>
    <div class="workbench hp-workbench" aria-label="Keep a progression visible by changing the radix">
      <div class="hp-presets enhancement" role="group" aria-label="Choose a progression">
        <button id="hp-powers" class="button" type="button" aria-pressed="true"><span>1/997</span><small>Keep tripling</small></button>
        <button id="hp-fibonacci" class="button" type="button" aria-pressed="false"><span>1/9899</span><small>Fibonacci</small></button>
        <button id="hp-counting" class="button" type="button" aria-pressed="false"><span>1/998001</span><small>Keep counting</small></button>
      </div>
      <div class="workbench-top"><h3 id="hp-title">Keep tripling.</h3><span id="hp-fraction" class="base-badge">1/997</span></div>
      <p id="hp-origin" class="hp-origin">1000 − 997 = 3. Reading in groups of three gives the powers 1, 3, 9, 27… before carrying.</p>
      <div id="hp-inscription" class="hp-inscription" role="math" aria-label="One over 997: six digits in radix 1000, then 729 in radix 998, 2187 in radix 2992, and 6561 in radix 8974; continue the tripling generator and balance rule">
        <span>0.</span><span id="hp-prefix-run" class="hp-token hp-prefix-run"><span id="hp-prefix">${runDigits(prefixRun)}</span><sub id="hp-prefix-base">1000</sub></span>
        <span id="hp-leading-dots" hidden aria-label="intermediate runs omitted">| …</span>${continuation.slice(0,3).map((row,i) => `<span class="hp-changed-run"><span class="hp-run-separator" aria-label="change radix">|</span><span id="hp-token-${i}" class="hp-token"${i === 0 ? ' aria-current="step"' : ''}><span id="hp-token-digit-${i}">⟨${row.desired}⟩</span><sub id="hp-token-radix-${i}">${row.radix}</sub></span></span>`).join("")}<span>| …</span>
      </div>
      <p id="hp-window-note" class="hp-notation-note" hidden>Middle runs are omitted from this excerpt; their radices still count in every weight.</p>
      <p id="hp-prefix-note" class="hp-notation-note">The first run keeps 6 digits in radix 1000; its final remainder is 729.</p>
      <p class="hp-notation-note">The highlighted run contains the selected digit. The final … continues the generator with the same balance rule.</p>
      <div class="hp-fork" aria-label="Compare the first changed digit"><div><span class="small-label">STAY IN RADIX <span id="hp-original-radix">1000</span></span><strong id="hp-fixed-first">731</strong><small>The next ordinary group</small></div><span class="hp-fork-or" aria-hidden="true">or</span><div><span class="small-label">CHANGE THE NEXT RADIX TO <span id="hp-first-radix">998</span></span><strong id="hp-changed-first">729</strong><small>The next term stays visible</small></div></div>
      <p id="hp-switch-note" class="hp-switch-note">The comparison above marks the first change. Use the arrows below to inspect the balance before and after it.</p>
      <div class="hp-steps enhancement"><button id="hp-previous" class="button icon-button" type="button" aria-label="Previous progression step">←</button><div class="position-slider"><label for="hp-position">Continue the pattern <strong id="hp-step-label">1 of 8</strong></label><input id="hp-position" type="range" min="-1" max="7" step="1" value="0"></div><button id="hp-next" class="button icon-button" type="button" aria-label="Next progression step">→</button></div>
      <div class="hp-balance-panel" aria-label="The balance check"><span class="small-label">TRY THE CURRENT RADIX</span><p id="hp-balance" class="run-equation">1000 × 729 − 997 × 729 = 2187</p><strong id="hp-decision">Change radix 1000 → 998</strong><p id="hp-reason">The leftover is at least 997. It would change the printed digit.</p><p id="hp-choice" class="run-equation">New radix = ⌊997 × 729 / 729⌋ + 1 = 998</p></div>
      <p id="hp-position-note" class="hp-position-note">Digit position 7 in this representation</p>
      <dl class="hp-readout"><div><dt>RADIX AT THIS POSITION</dt><dd id="hp-radix">998</dd></div><div><dt>DIGIT WRITTEN</dt><dd id="hp-digit">729</dd></div><div><dt>REMAINDER</dt><dd id="hp-remainder">729 → 729</dd></div></dl>
      <p id="hp-equation" class="run-equation">998 × 729 = 997 × 729 + 729</p>
      <p id="hp-observation" class="hp-observation" aria-live="polite">Next comes 2187. The same balance check decides whether to keep or change the radix.</p>
      <details id="hp-weights" class="math-note"><summary>How do the new digits keep the same value?</summary>
        <p>A digit’s weight is 1 divided by the product of <em>all</em> radices used through its position. Keep the old prefix, then add the new contributions:</p>
        <p id="hp-first-weights" class="formula">729/(1000⁶ × 998) + 2187/(1000⁶ × 998 × 2992) + …</p>
        <p id="hp-weight-explanation">The first new digit is 729, weighted by 1/(1000⁶ × 998). Every step refines the remaining tail.</p>
        <p id="hp-accounting" class="formula">997Q + 729 = P<br>Q/P + 729/(997P) = 1/997</p>
        <p>P is the product of the radices so far; Q/P is the value written so far. The remaining fraction fills the gap exactly. Its value tends to zero, so the complete expansion is the original fraction.</p>
        <details id="hp-exact"><summary>Inspect the exact integers at this step</summary><label class="run-state-label" for="hp-place">Place product P<textarea id="hp-place" rows="3" readonly spellcheck="false">${handoff.after.place}</textarea></label><label class="run-state-label" for="hp-quotient">Packed quotient Q<textarea id="hp-quotient" rows="3" readonly spellcheck="false">${handoff.after.quotient}</textarea></label><p id="hp-decimal-prefix" class="fine-print">Written prefix, truncated to 20 decimal places: ${decimalTruncation(handoff.after.quotient,handoff.after.place)}…</p></details>
      </details>
      <div class="position-sharing enhancement"><button id="hp-share" class="button small" type="button">Copy a link to this step</button><span id="hp-share-help">Keep this example and position.</span><label id="hp-share-label" class="share-link-fallback" for="hp-share-link" hidden>Copy this link:<input id="hp-share-link" type="text" readonly spellcheck="false" aria-label="Link to the selected progression step"></label></div>

    </div>
    ${renderNotationExamples()}
    <details id="hp-proof" class="math-note"><summary>The balance rule and its Lean proofs</summary>
      <p>The <a href="${atlas}#unified_balance_rule">proof-status atlas</a> records the balance rule as <strong>reproved-here in Lean</strong>. Supply the denominator D, current remainder 0 &lt; r &lt; D, current radix B ≥ 2, and next progression term a ≥ 0.</p>
      <p class="formula">T = Br − Da<br>0 &lt; T &lt; D: keep B and continue.<br>T = 0: keep B and finish.<br>Otherwise, for a &gt; 0: R = ⌊Da/r⌋ + 1.</p>
      <p>The floor symbol means round down. The replacement is the smallest radix writing the positive target with a positive remainder. An accepted zero term is allowed; a rejected zero needs a separate feasibility check.</p>
      <p><a href="${handoffProof}">BalanceRule.lean</a> proves legal digits, prefix and value preservation, completion, and convergence of the written stream. Its stream theorem assumes positive targets after any separately certified initial zeros. The sequence is supplied: tripling, Fibonacci, or counting. The denominator alone does not select a unique progression.</p>
    </details>
    <details id="notation-reference" class="math-note"><summary>Notation reference: exact meaning and proof map</summary>
      <p>The <a href="${atlas}#mixed_radix_run_value_preservation">registered run-accounting claim</a> supplies the mathematical meaning. Angle brackets, commas, and bars are our display convention (<strong>implemented-here</strong>). The underlying run and value identities are <strong>reproved-here in Lean</strong>; the typography and browser are not formally verified.</p>
      <p>A run ⟨d₁, …, d<sub>L</sub>⟩<sub>B</sub> contains L digits, each with 0 ≤ d &lt; B. Use B once for <em>each digit</em>, not once for the whole bracket. If P is the place product before the run and H = d₁B<sup>L−1</sup> + … + d<sub>L</sub>, its contribution is:</p>
      <p class="formula">H / (P × B<sup>L</sup>)</p>
      <p>For A/D, start with P = 1, Q = 0, r = A (0 ≤ A &lt; D). Each written digit d in radix B updates P′ = PB, Q′ = BQ + d, r′ = Br − Dd. The certificate stays:</p>
      <p class="formula">DQ + r = AP<br>A/D = Q/P + r/(DP).</p>
      <p>A finite displayed prefix needs its remaining tail. An ending … is an instruction to continue the named generator and balance rule; it is not a zero tail. Inside the counting run, … abbreviates every integer between the displayed endpoints.</p>
      <dl class="notation-proof-map">
        <dt>Run digits → weighted value</dt><dd><a href="https://github.com/mikedotexe/reptends/blob/main/lean/RadixRuns/Encoding.lean">Run.packed_eq_horner; Run.digitValue_eq_packed</a></dd>
        <dt>Runs and radix changes preserve value</dt><dd><a href="https://github.com/mikedotexe/reptends/blob/main/lean/RadixRuns/Core.lean">DivisionState.advance_prefix_value; DivisionState.advance_value; DivisionState.radix_change_preserves_value</a></dd>
        <dt>Balance decisions, completion, infinite value</dt><dd><a href="${handoffProof}">RadixBalance.chosen_digit_legal; chosen_preserves_prefix; zero_finishes; completed_stays_completed; after_prefix_hasSum</a></dd>
      </dl>
      <p>All three examples and their first eight changed steps are embedded in <code>script#reptends-notation</code> as non-executable JSON: schema, generators, complete run digits, radix decisions, and proof references. Large integers are strings. This is a reproducible data record, not a proof-assistant certificate. <a href="https://github.com/mikedotexe/reptends/blob/main/essay/NOTATION.md">Read the standalone notation specification</a>.</p>
    </details>
    <details id="hp-finish" class="math-note"><summary>What if the remainder reaches zero?</summary>
      <p>Zero is a successful finish. For 1/8, ordinary decimal division reaches the prefix 0.12 with remainder 4. Writing the next digit 5 gives:</p>
      <p class="formula">10 × 4 − 8 × 5 = 0<br>0.125 = 1/8 exactly.</p>
      <p>In our notation, this is 0.⟨1, 2, 5⟩<sub>10</sub>, with remainder 0. Keep radix 10 and stop, or append zero digits in the same radix forever. A generating sequence can still be examined on its own, but further positive terms cannot be added to this completed expansion.</p>
    </details>
    <details id="run-from-start" class="math-note hp-original"><summary>Start with changing units from the beginning</summary>
      <p>We can also begin 1/997 with remainder 1 and change the radix from the first digit. This gives the full power stream 1, 3, 9, 27… with another set of weights.</p>
    <div class="run-inscription" role="math" aria-label="One over 997: digit 1 in radix 998, digit 3 in radix 2992, digit 9 in radix 8974, digit 27 in radix 26920, and so on">
      <span>0.</span>${first.map(row => `<span class="run-token"><span class="run-symbol"><span>⟨${row.packed}⟩</span><sub>${row.radix}</sub></span><span class="run-bar" aria-hidden="true">|</span></span>`).join("")}<span>…</span>
    </div>
    <p class="run-caption">Each bar changes the radix. In this particular construction, the remainder also returns to 1 after every digit.</p>
    <div class="workbench radix-workbench" aria-label="Explore the changing radix of 1 over 997">
      <div class="workbench-top"><h3>Same remainder.<br>More room.</h3><span class="base-badge">1/997 · one digit per run</span></div>
      <div class="position-controls enhancement">
        <button id="run-previous" class="button icon-button" type="button" aria-label="Previous run">←</button>
        <div class="position-slider"><label for="run-position">Selected run <strong id="run-position-label">4 of 169</strong></label><input id="run-position" type="range" min="0" max="168" step="1" value="3"></div>
        <button id="run-next" class="button icon-button" type="button" aria-label="Next run">→</button>
      </div>
      <dl class="run-readout"><div><dt>RADIX</dt><dd id="run-radix">26920</dd></div><div><dt>EMITTED DIGIT</dt><dd id="run-digit">27</dd><small id="run-power">3³</small></div><div><dt>REMAINDER</dt><dd>1 → 1</dd><small>returns after one digit</small></div></dl>
      <p id="run-equation" class="run-equation">26920 × 1 = 997 × 27 + 1</p>
      <p id="run-size-note" class="fine-print">Each emitted digit fits in its radix.</p>
      <div class="run-jumps enhancement"><button id="run-start" class="button small" type="button">First four runs</button><button id="run-166" class="button small" type="button">Inspect 3¹⁶⁶</button></div>
      <p id="run-observation" class="run-observation" aria-live="polite">The next run uses a larger radix and emits 81. The remainder will still be 1.</p>
      <details id="run-state" class="math-note"><summary>Inspect the exact state and its remaining tail</summary>
        <p id="run-state-heading">After 4 runs: P has ${selected.after.place.toString().length} digits. The prefix is Q/P; the tail is 1/(997 × P).</p>
        <dl class="exact-values"><div><dt>Radix B</dt><dd id="run-exact-radix">26920</dd></div><div><dt>Emitted digit</dt><dd id="run-exact-digit">27</dd></div></dl>
        <label class="run-state-label" for="run-place">Accumulated place product P<textarea id="run-place" rows="3" readonly spellcheck="false">${selected.after.place}</textarea></label>
        <label class="run-state-label" for="run-quotient">Packed quotient Q<textarea id="run-quotient" rows="3" readonly spellcheck="false">${selected.after.quotient}</textarea></label>
        <p class="formula">997Q + 1 = P<br>Q/P + 1/(997P) = 1/997</p>
      </details>
      <div class="position-sharing enhancement"><button id="share-run" class="button small" type="button">Copy a link to this run</button><span id="share-run-help">Keep this exact step.</span><label id="share-run-label" class="share-link-fallback" for="share-run-link" hidden>Copy this link:<input id="share-run-link" type="text" readonly spellcheck="false" aria-label="Link to the selected run"></label></div>
    </div>
    <p class="chapter-bridge">The powers were already infinite. This representation makes each one a separate digit, with a new weight.</p>
    <details id="run-decimals" class="math-note"><summary>What does this add up to in ordinary decimal?</summary>
      <p>The first two contributions are 1/998 + 3/(998 × 2992). Add contributions with their weights; do not concatenate their decimal spellings.</p>
      <div class="run-table-wrap"><table class="run-table"><caption>Accumulated values, truncated after 20 decimal places</caption><thead><tr><th scope="col">Runs</th><th scope="col">Last digit</th><th scope="col">Written prefix Q/P</th></tr></thead><tbody>${rows}</tbody></table></div>
      <p>Each row leaves the positive tail 1/(997P). Including every run gives 1/997 = ${decimalTruncation(1n,997n)}… .</p>
    </details>
    <details id="run-proof" class="math-note"><summary>The two equations, and what Lean proves</summary>
      <p>The <a href="${atlas}">proof-status atlas</a> labels the run accounting and power construction <strong>reproved-here in Lean</strong>.</p>
      <p>For any integers D &gt; 1 and c ≥ 2, choose the radix B<sub>n</sub> = Dc<sup>n</sup> + 1. Then B<sub>n</sub> × 1 = D × c<sup>n</sup> + 1: the emitted digit is c<sup>n</sup>, and the remainder is 1.</p>
      <p>The weights and run accounting use the <a href="#notation-reference">same notation reference</a>. Here every finite prefix has positive tail 1/(997P), and the full sum is 1/997. <a href="${proof}">Read the worked power proofs</a>. This optional construction starts changing units immediately; the main examples keep their original prefix first.</p>
    </details>
    </details>
    ${renderNotationCertificate()}
  </section>`;
}
