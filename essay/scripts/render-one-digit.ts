/** A complete, readable example without JavaScript or a notation prerequisite. */
export function renderOneDigitChapter(): string {
  return `<section id="one-digit" class="chapter wrap" aria-labelledby="one-digit-title" tabindex="-1">
    <div class="chapter-heading"><span class="chapter-number">05 / GROUP THE WHOLE LOOP</span><h2 id="one-digit-title">Could the whole block<br>be one digit?</h2></div>
    <div class="prose"><p>We already read three decimal digits at a time by using base 1000. What if a place held an entire repeating block?</p><p>Use a shorter example to see it all at once: <strong>1/7 = 0.<span class="repeating-digits">142857</span></strong>. The bar says to repeat those six digits. In base one million, those six digits fit into <em>one</em> place.</p></div>
    <div class="whole-block-comparison">
      <figure><figcaption>Base 10 · six steps</figcaption><div class="decimal-tiles" aria-label="Six digits: 1, 4, 2, 8, 5, 7">${[1,4,2,8,5,7].map(d => `<span>${d}</span>`).join("")}</div><p>Each place is one tenth of the previous place.</p><p class="block-remainders">Remainders: 1, 3, 2, 6, 4, 5, <strong>1</strong></p></figure>
      <figure><figcaption>Base 1,000,000 · one step</figcaption><div class="block-tile" aria-label="One digit whose value is 142857">142857</div><p>Each place is one millionth of the previous place.</p><p class="block-remainders">Remainders: 1, <strong>1</strong></p></figure>
    </div>
    <div class="block-division"><p class="small-label">THE SAME RETURN, IN ONE STEP</p><p class="equation">1,000,000 × 1 = 7 × 142857 + 1</p><p>Write the digit <strong>142857</strong>. Keep remainder <strong>1</strong>. The next step has the same starting remainder, so it writes 142857 again.</p></div>
    <p class="block-repetition" aria-label="In base one million, one over seven is zero point, digit 142857 repeated">0. <span>142857</span> <span>142857</span> <span>142857</span> …</p>
    <p class="block-caption">One box is one digit in base 1,000,000. Its six printed characters spell that digit’s value.</p>
    <div class="prose"><p>The value is still 1/7. We have changed the size of a place. The repeating bar can be read as an instruction to group the whole loop into one digit.</p></div>
    <details class="math-note"><summary>Check the value of the grouped digits</summary><p>The <a href="https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md#mixed_radix_run_value_preservation">run-accounting proof</a> records how grouping preserves place values. Here six base-10 steps have place product 10⁶ = 1,000,000 and packed digit 142857. The displayed equality is exact integer arithmetic.</p><p class="formula">142857 / 1,000,000 + 142857 / 1,000,000² + …<br>= 142857 / 999999 = 1/7.</p></details>
    <p class="chapter-bridge">We can choose the size of a place. <a href="#change-radix">Can we choose each next place so the powers of three stay visible?</a></p>
  </section>`;
}
