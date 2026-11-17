import { decimalTruncation, powerRuns } from "../src/run-radices.ts";
import { progressionRows } from "../src/math/progression.ts";

const atlas = "https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md";
const proof = "https://github.com/mikedotexe/reptends/blob/main/lean/RadixRuns/Examples.lean";
const handoffProof = "https://github.com/mikedotexe/reptends/blob/main/lean/RadixRuns/HandoffSearch.lean";

/** Both worked examples remain readable without JavaScript. */
export function renderRadixChapter(): string {
  const first = powerRuns(997n, 3n, 4);
  const rows = first.map((row, n) => `<tr><th scope="row">${n + 1}</th><td>${row.packed}</td><td>${decimalTruncation(row.after.quotient, row.after.place)}…</td></tr>`).join("");
  const selected = first[3]!;
  const continuation = progressionRows("powers", 8);
  const handoff = continuation[0]!;
  return `<section id="change-radix" class="chapter wrap radix-chapter" aria-labelledby="radix-title" tabindex="-1">
    <div class="chapter-heading"><span class="chapter-number">04 / CHANGE THE RADIX</span><h2 id="radix-title">Keep the pattern.<br>Change the units.</h2></div>
    <div class="prose"><p>For 1/997, tripling gives 1, 3, 9, 27, 81, 243, 729… . The decimal groups show that pattern until carrying turns 729 into 731.</p>
      <p>We can keep the groups already written and change the <strong>radix</strong>—the base used for the next digit. This <a href="${atlas}#retained_progression_handoffs">value-preserving construction</a> makes room for the same progression to stay visible.</p></div>
    <div class="workbench hp-workbench" aria-label="Keep a progression visible by changing the radix">
      <div class="hp-presets enhancement" role="group" aria-label="Choose a progression">
        <button id="hp-powers" class="button" type="button" aria-pressed="true"><span>1/997</span><small>Keep tripling</small></button>
        <button id="hp-counting" class="button" type="button" aria-pressed="false"><span>1/998001</span><small>Keep counting</small></button>
      </div>
      <div class="workbench-top"><h3 id="hp-title">Keep tripling.</h3><span id="hp-fraction" class="base-badge">1/997</span></div>
      <p id="hp-origin" class="hp-origin">1000 − 997 = 3. Reading in groups of three gives the powers 1, 3, 9, 27… before carrying.</p>
      <div class="hp-prefix"><span class="small-label">KEEP WHAT IS ALREADY WRITTEN</span><p id="hp-prefix">001 · 003 · 009 · 027 · 081 · 243</p><small id="hp-prefix-note">6 digits in radix 1000; the remainder is 729.</small></div>
      <div class="hp-fork" aria-label="Compare the first changed digit"><div><span class="small-label">STAY IN RADIX 1000</span><strong id="hp-fixed-first">731</strong><small>The next ordinary group</small></div><span class="hp-fork-or" aria-hidden="true">or</span><div><span class="small-label">CHANGE THE NEXT RADIX TO <span id="hp-first-radix">998</span></span><strong id="hp-changed-first">729</strong><small>The next term stays visible</small></div></div>
      <p id="hp-switch-note" class="hp-switch-note">This first switch keeps remainder 729. Each later step triples the digit and uses a new radix.</p>
      <div class="hp-steps enhancement"><button id="hp-previous" class="button icon-button" type="button" aria-label="Previous changed-radix digit" disabled>←</button><div class="position-slider"><label for="hp-position">Continue the pattern <strong id="hp-step-label">1 of 8</strong></label><input id="hp-position" type="range" min="0" max="7" step="1" value="0"></div><button id="hp-next" class="button icon-button" type="button" aria-label="Next changed-radix digit">→</button></div>
      <p id="hp-position-note" class="hp-position-note">Digit position 7 in this representation</p>
      <dl class="hp-readout"><div><dt>RADIX AT THIS POSITION</dt><dd id="hp-radix">998</dd></div><div><dt>DIGIT WRITTEN</dt><dd id="hp-digit">729</dd></div><div><dt>REMAINDER</dt><dd id="hp-remainder">729 → 729</dd></div></dl>
      <p id="hp-equation" class="run-equation">998 × 729 = 997 × 729 + 729</p>
      <div id="hp-inscription" class="hp-inscription" role="math" aria-label="After the preserved prefix: digit 729 in radix 998, digit 2187 in radix 2992, digit 6561 in radix 8974, and so on"><span id="hp-leading-dots" hidden>…</span>${continuation.slice(0,3).map((row,i) => `<span id="hp-token-${i}" class="hp-token"${i === 0 ? ' aria-current="step"' : ''}><span id="hp-token-digit-${i}">[${row.desired}]</span><sub id="hp-token-radix-${i}">${row.radix}</sub></span>`).join("")}<span>…</span></div>
      <p class="hp-notation-note">After the preserved prefix, each bracket is one digit. The small number below it is its radix.</p>
      <p id="hp-observation" class="hp-observation" aria-live="polite">Next comes 2187. Tripling can continue indefinitely as the units change.</p>
      <details id="hp-weights" class="math-note"><summary>How do the new digits keep the same value?</summary>
        <p>A digit’s weight is 1 divided by the product of <em>all</em> radices used through its position. Keep the old prefix, then add the new contributions:</p>
        <p id="hp-first-weights" class="formula">729/(1000⁶ × 998) + 2187/(1000⁶ × 998 × 2992) + …</p>
        <p id="hp-weight-explanation">The first new digit is 729, weighted by 1/(1000⁶ × 998). Every step refines the remaining tail.</p>
        <p id="hp-accounting" class="formula">997Q + 729 = P<br>Q/P + 729/(997P) = 1/997</p>
        <p>P is the product of the radices so far; Q/P is the value written so far. The remaining fraction fills the gap exactly. Its value tends to zero, so the complete expansion is the original fraction.</p>
        <details id="hp-exact"><summary>Inspect the exact integers at this step</summary><label class="run-state-label" for="hp-place">Place product P<textarea id="hp-place" rows="3" readonly spellcheck="false">${handoff.after.place}</textarea></label><label class="run-state-label" for="hp-quotient">Packed quotient Q<textarea id="hp-quotient" rows="3" readonly spellcheck="false">${handoff.after.quotient}</textarea></label><p id="hp-decimal-prefix" class="fine-print">Written prefix, truncated to 20 decimal places: ${decimalTruncation(handoff.after.quotient,handoff.after.place)}…</p></details>
      </details>
      <div class="position-sharing enhancement"><button id="hp-share" class="button small" type="button">Copy a link to this step</button><span id="hp-share-help">Keep this example and position.</span><label id="hp-share-label" class="share-link-fallback" for="hp-share-link" hidden>Copy this link:<input id="hp-share-link" type="text" readonly spellcheck="false" aria-label="Link to the selected progression step"></label></div>
      <noscript><p class="hp-static-counting"><strong>Keep counting with 1/998001.</strong> In radix 1000, the groups are 000, 001, …, 997, then 999. Preserve the first 998 groups and use radix 999 to write 998. Radices 998002, 999001, 1000000 then write 999, 1000, 1001. The same value is expressed with new weights.</p></noscript>
    </div>
    <p class="chapter-bridge">The progression stays visible. The value stays fixed.<br>The new digits have new weights.</p>
    <details id="hp-proof" class="math-note"><summary>The general rule, and what Lean proves</summary>
      <p>The <a href="${atlas}#retained_progression_handoffs">proof-status atlas</a> records this construction as <strong>reproved-here in Lean</strong>. It works with integer arithmetic, independently of how we print the numbers.</p>
      <p>Let D be the denominator, r the current positive remainder, and d the next positive term of the progression. Use:</p>
      <p class="formula">Next radix = ⌊Dd/r⌋ + 1<br>Next remainder = (next radix) × r − Dd</p>
      <p>The floor symbol ⌊ ⌋ means round down. This is the smallest radix that writes d and leaves a positive remainder. Each new digit fits its radix, the prefix and remaining tail preserve the value, and the infinite continuation sums to the starting fraction.</p>
      <p>For 1/997, 1000 − 997 = 3 supplies the tripling pattern. For 1/998001, 998001 = 999² supplies the counting pattern in groups of three. We continue those existing coefficient sequences with new place values. The rule also accepts other positive sequences; the denominator alone does not pick a unique one.</p>
      <p>A switch need not wait for a repeated remainder: the counting example first changes the remainder to 999, then keeps returning to it. <a href="${handoffProof}">Read the value-preservation and convergence proofs</a>. Lean verifies the mathematical construction; the interactive implementation is checked separately.</p>
    </details>
    <details id="run-from-start" class="math-note hp-original"><summary>Start with changing units from the beginning</summary>
      <p>We can also begin 1/997 with remainder 1 and change the radix from the first digit. This gives the full power stream 1, 3, 9, 27… with another set of weights.</p>
    <div class="run-inscription" role="math" aria-label="One over 997: digit 1 in radix 998, digit 3 in radix 2992, digit 9 in radix 8974, digit 27 in radix 26920, and so on">
      <span>0.</span>${first.map(row => `<span class="run-token"><span class="run-symbol"><span>[${row.packed}]</span><sub>${row.radix}</sub></span><span class="run-bar" aria-hidden="true">|</span></span>`).join("")}<span>…</span>
    </div>
    <p class="run-caption">Every bar marks remainder 1 returning. That is where we choose the next radix.</p>
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
      <p>A <strong>run</strong> can also contain several digits in one radix B. If its length is L, its packed integer is A, and earlier radices have product P, its contribution is:</p>
      <p class="formula">A / (P × B<sup>L</sup>)</p>
      <p>At a return to remainder R, that contribution equals (R/D)(1/P − 1/(PB<sup>L</sup>)). It consumes exactly the difference between the old and new tails.</p>
      <p>Lean proves preservation across arbitrary valid runs and radix changes. For the power construction it proves legal digits, one-digit first returns, and a positive tail at every finite stage. The tail tends to zero, so the infinite sum is exactly 1/D. The argument is independent of the base used to print the integers.</p>
      <p>Changing radices changes the weights of the powers. This is a chosen representation, not a uniquely preferred form or a claim that ordinary decimal division loses terms. <a href="${proof}">Read the 997 proofs</a> or the <a href="${atlas}">registered claims and their scope</a>. The bracket-and-bar notation is an explanatory convention; the run records and arithmetic are formalized.</p>
    </details>
    </details>
  </section>`;
}
