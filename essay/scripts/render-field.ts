import { renderFieldReading, renderFieldRuler } from "../src/field-view.ts";

export function renderFieldChapter(): string {
  return `<section id="nearby-fractions" class="chapter field-chapter wrap" aria-labelledby="field-title" tabindex="-1">
    <div class="chapter-heading"><span class="chapter-number">07 / MEET THE NEIGHBOURS</span><h2 id="field-title">Does 997<br>have company?</h2></div>
    <div class="prose"><p>Keep the three-digit boxes. This time, change the denominator. Nearby fractions have progressions of their own, and we can draw the neighbourhood where those progressions begin clearly.</p></div>
    <div class="field-lesson" id="field-lesson">
      <div class="field-steps enhancement" role="group" aria-label="Explore the field in three steps">
        <button type="button" data-field-go="1" aria-pressed="true">Start at 997</button>
        <button type="button" data-field-go="2" aria-pressed="false">Meet the neighbours</button>
        <button type="button" data-field-go="3" aria-pressed="false">Open the strip</button>
      </div>
      <div data-field-panel="1" class="field-panel">
        <h3>Three below a thousand.</h3><p>We know this one: <strong>997 = 1000 − 3</strong>. Before carrying, its three-digit places receive 1, 3, 9, 27, … .</p>
        <div class="field-groups" aria-label="The first six groups of one over 997"><span>001</span><span>003</span><span>009</span><span>027</span><span>081</span><span>243</span></div>
        <div class="field-static-ruler">${renderFieldRuler(997, 1)}</div>
        <p class="field-takeaway">Move to 998 and the gap is 2. Its progression doubles. Move to 999 and the gap is 1. Its groups repeat 001.</p>
      </div>
      <div data-field-panel="2" class="field-panel">
        <h3>A neighbourhood of progressions.</h3><p>How far can we move and still see the pattern in the first two boxes? For this three-digit reading, square the distance from 1000. If that square is smaller than the denominator, we are inside its <strong>field</strong>.</p>
        <p class="field-inline-equation">At 997: <strong>3² = 9 &lt; 997</strong>.</p>
        <div class="field-static-ruler">${renderFieldRuler(997, 2)}</div>
        <p class="field-takeaway">The whole-number members run from <strong>969 through 1032</strong>. Above 1000 the series alternates, so its opening boxes include borrowing. Some members terminate; this field describes how an expansion starts.</p>
      </div>
      <div data-field-panel="3" class="field-panel">
        <h3>Change the ruler. See one unit.</h3><p>Keep every denominator in the same field, but place it by its <strong>square root</strong>. Our familiar 997 now sits at √997 ≈ 31.5753. Watch what happens to the two boundaries.</p>
        <div class="field-static-ruler">${renderFieldRuler(997, 3)}</div>
        <p class="field-takeaway">They become <strong>31.126729… and 32.126729…</strong>: exactly one unit apart. The fractions have not changed. We have found a ruler that makes this field’s width simple.</p>
      </div>
      <div id="field-live-ruler" class="field-live-ruler" hidden></div>
      <div id="field-inspector" class="field-inspector">
        <div class="field-controls enhancement">
          <label for="field-denominator">Choose a denominator <output id="field-denominator-value" for="field-denominator">997</output></label>
          <input id="field-denominator" type="range" min="968" max="1033" step="1" value="997" aria-describedby="field-slider-help">
          <p id="field-slider-help">Use the slider or its arrow keys. Try a neighbour, then an edge.</p>
          <div class="field-presets" role="group" aria-label="Fractions to compare"><button type="button" data-field-n="997">997</button><button type="button" data-field-n="998">998</button><button type="button" data-field-n="1003">1003</button><button type="button" data-field-n="969">First: 969</button><button type="button" data-field-n="968">Outside: 968</button><button type="button" data-field-n="1033">Outside: 1033</button></div>
        </div>
        <div id="field-reading" class="field-reading">${renderFieldReading(997)}</div>
      </div>
      <div class="field-next-row enhancement"><button id="field-next" type="button" class="button primary">Reveal its neighbours</button><span id="field-step-count">Step 1 of 3</span></div>
      <p id="field-status" class="sr-only" aria-live="polite" aria-atomic="true"></p>
    </div>
    <details id="field-boundaries" class="math-note field-proof"><summary>Why is the strip exactly one unit wide?</summary>
      <div class="prose"><p>This is a worked algebraic calculation for the landmark 1000. The <a href="https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md#field-around-1000-worked-example">proof-status record</a> separates this implemented example from the site’s Lean proofs.</p>
      <p>Write n for the denominator. The boundary is where the squared gap just equals n:</p><p class="formula">(1000 − n)² = n.</p>
      <p>On the square-root ruler, call the lower boundary x and the upper boundary y. The equations become:</p><p class="formula">x² + x = 1000<br>y² − y = 1000.</p>
      <p>If x fits the first equation, <strong>y = x + 1</strong> fits the second, because (x + 1)² − (x + 1) = x² + x. So the positive boundary roots differ by exactly 1.</p>
      <p class="formula">x = (√4001 − 1)/2 = 31.126729…<br>y = (√4001 + 1)/2 = 32.126729…</p>
      <p>Squaring gives the ordinary-number boundaries <strong>968.873270… and 1032.126729…</strong>. The field is strictly between them. That is why 969 is the first whole-number member and 1032 is the last.</p>
      <p>The first two boxes can be checked directly. Below 1000, put k = 1000 − n. After 001, division writes k + floor(k²/n), so the next box remains k precisely when k² &lt; n. Above 1000, put d = n − 1000. After 000, the next box is 1000 − d + floor(d²/n); the same condition preserves the borrowed opening.</p></div>
    </details>
    <p class="chapter-bridge">The gap that gave us a progression also gave us a place on a ruler. We can now find 997 inside a whole neighbourhood, and see exactly where that neighbourhood ends.</p>
  </section>`;
}
