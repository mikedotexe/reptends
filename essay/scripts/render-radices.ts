import { decimalTruncation, powerRuns } from "../src/run-radices.ts";

const atlas = "https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md";
const proof = "https://github.com/mikedotexe/reptends/blob/main/lean/RadixRuns/Examples.lean";

/** The main example and its explanation remain available without JavaScript. */
export function renderRadixChapter(): string {
  const first = powerRuns(997n, 3n, 4);
  const rows = first.map((row, n) => `<tr><th scope="row">${n + 1}</th><td>${row.packed}</td><td>${decimalTruncation(row.after.quotient, row.after.place)}…</td></tr>`).join("");
  const selected = first[3]!;
  return `<section id="change-radix" class="chapter wrap radix-chapter" aria-labelledby="radix-title" tabindex="-1">
    <div class="chapter-heading"><span class="chapter-number">04 / CHANGE THE RADIX</span><h2 id="radix-title">Let the measuring<br>units grow.</h2></div>
    <div class="prose"><p>Adding nines gave each decimal group more room. Could we keep <strong>1/997</strong> fixed and make new room as we go?</p>
      <p>Let the <strong>radix</strong>—the base used at a position—change. In <a href="${atlas}">this exact construction</a>, each bracket holds one digit; the number beneath it gives that position’s radix.</p></div>
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
    <ul class="run-principles"><li><strong>Keep the value fixed.</strong> The written prefix and its remaining tail always add to 1/997.</li><li><strong>Keep each digit’s weight.</strong> Multiply all the radices used so far to find its place.</li><li><strong>Mark the return.</strong> A repeated remainder can come with a new radix and a finer unit.</li><li><strong>Keep making room.</strong> Here the radix grows alongside the power, so every power fits as one legal digit.</li></ul>
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
  </section>`;
}
