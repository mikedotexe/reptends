import { formatWord } from "./math/lifts.ts";
import { buildUnfoldedView, certifiedPrefix } from "./math/unfolded-notation.ts";
import { initGeometry } from "./geometry.ts";
import { positionFromSearch, linkToPosition } from "./navigation.ts";

const view = buildUnfoldedView({ base: 1000n, coefficients: [3n] }, 332);
const certificates = view.rows.map((_, index) => certifiedPrefix(view.trace, index + 1));
const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)");
const initialPosition = positionFromSearch(window.location.search);
let selected = initialPosition ?? 6;
let revealed = initialPosition !== null;
let animationFrame = 0;

function element<T extends HTMLElement>(id: string): T {
  const found = document.getElementById(id);
  if (!found) throw new Error("Missing essay element: " + id);
  return found as T;
}
function put(id: string, value: string | bigint): void {
  element(id).textContent = String(value);
}
function compact(value: bigint): string {
  const digits = value.toString();
  return digits.length <= 12 ? digits : digits.slice(0, 6) + "…" + digits.slice(-4);
}
function superscript(value: number): string {
  return String(value).replace(/[0-9]/g, digit => "⁰¹²³⁴⁵⁶⁷⁸⁹"[Number(digit)]!);
}
function word(value: bigint): string {
  return formatWord(value, 1000n);
}
function announce(message: string): void {
  put("live-status", message);
}

function renderReveal(): void {
  put("hero-answer", revealed ? "731" : "?");
  put("hero-explanation", revealed
    ? "729 still fits into three digits. So why did it become 731?"
    : "Multiply 243 by three. What would you expect next?");
  put("reveal", revealed ? "Follow the hidden carry ↓" : "Reveal the next group ↗");
}

function rememberPosition(): void {
  // file:// copies keep their offline location; copied links still target the public essay.
  if (window.location.protocol !== "https:" && window.location.protocol !== "http:") return;
  const url = new URL(window.location.href);
  url.searchParams.set("group", String(selected + 1));
  try {
    // Replace rather than append for a scrubber: a drag must not fill browser history.
    history.replaceState(null, "", url);
  } catch {
    // History may be restricted in an embedded preview. The arithmetic remains usable.
  }
}

/** All Number conversions below are bounded remainders or drawing coordinates. */
function drawSplit(progress: number): void {
  const row = view.rows[selected]!;
  const count = Number((3n * row.remainder) / 997n); // 0, 1, or 2.
  const left = Number(row.nextRemainder); // 0 through 996.
  const svg = document.getElementById("split-svg")!;
  svg.setAttribute("aria-label", String(3n * row.remainder) + " splits into " + count + " full groups of 997 and a remainder of " + left);
  const y = 22 + progress * 77;
  let drawing = '<text x="12" y="16" font-size="13">Three times the remainder</text>';
  for (let index = 0; index < 3; index++) {
    drawing += '<rect x="' + (12 + index * 188) + '" y="22" width="182" height="48" rx="5" fill="none" stroke="#c3ccbc" stroke-dasharray="4 4"/>';
  }
  for (let index = 0; index < count; index++) {
    const x = 12 + index * 188;
    drawing += '<rect x="' + x + '" y="' + y + '" width="182" height="48" rx="5" fill="#e6d3b1"/><text x="' + (x + 91) + '" y="' + (y + 31) + '" text-anchor="middle" font-size="21">997</text>';
  }
  const remainderX = 12 + count * 188 + (388 - (12 + count * 188)) * progress;
  const remainderWidth = 182 * left / 997;
  drawing += '<rect x="' + remainderX + '" y="' + y + '" width="' + remainderWidth + '" height="48" rx="3" fill="#8db8a9"/>';
  drawing += '<text x="' + remainderX + '" y="' + (y + 70) + '" font-size="17">' + left + ' left</text>';
  if (progress > 0.5) drawing += '<text x="12" y="185" font-size="13">' + count + ' whole group' + (count === 1 ? '' : 's') + ' → add ' + count + ' to the printed word</text>';
  svg.innerHTML = drawing;
}

function stopAnimation(): void {
  cancelAnimationFrame(animationFrame);
  animationFrame = 0;
  element<HTMLButtonElement>("animate-split").removeAttribute("aria-disabled");
}

function render(message?: string): void {
  stopAnimation();
  const row = view.rows[selected]!;
  const certificate = certificates[selected]!;
  const slider = element<HTMLInputElement>("position");
  slider.value = String(selected);
  slider.setAttribute("aria-valuetext", "Group " + (selected + 1) + " of 332: " + word(row.word));
  element<HTMLInputElement>("share-link").value = linkToPosition(selected);
  element("share-link-label").hidden = true;
  put("share-position", "Copy link to this group");
  put("share-help", "Send someone straight to the selected group.");
  put("position-label", (selected + 1) + " of 332");
  element<HTMLButtonElement>("previous").disabled = selected === 0;
  element<HTMLButtonElement>("next").disabled = selected === 331;
  for (const [suffix, offset] of [["before", -1], ["current", 0], ["after", 1]] as const) {
    const neighbor = view.rows[selected + offset];
    put("place-" + suffix, neighbor ? "Group " + neighbor.placeIndex : "—");
    put("raw-" + suffix, neighbor ? (neighbor.raw < 1000n ? neighbor.displayedTerm : compact(neighbor.raw)) : "—");
    put("word-" + suffix, neighbor ? word(neighbor.word) : "—");
  }
  put("carry-equation", compact(row.raw) + " + " + compact(row.carryIn) + " − 1000 × " + compact(row.quotient) + " = " + word(row.word));
  put("carry-description", selected === 6
    ? "Two whole units arrive from the remaining tail. No earlier carry needs exchanging yet."
    : selected === 7
      ? "The next tail contributes 6. But the previous carry of 2 was already spent one place to the left: subtract 2000 here. That leaves 193."
      : row.quotient === 0n
        ? "The remaining tail has not crossed a group boundary yet. The growing term and the printed group agree."
        : "Add the incoming carry, then subtract 1000 times the previous carry. Each previous unit was already accounted for one place to the left.");
  element("abbreviation-note").hidden = row.raw.toString().length <= 12 && row.carryIn.toString().length <= 12;
  put("exact-raw", row.raw);
  put("exact-carry", row.carryIn);
  put("exact-previous", row.quotient);
  put("exact-division", "1000 × " + row.remainder + " = 997 × " + row.word + " + " + row.nextRemainder);
  put("prefix-check", "After " + certificate.terms + " terms, the raw prefix leaves the exact balance " + certificate.stateAfterPrefix + " / (997 × 1000" + superscript(certificate.terms) + "). Settling it adds " + certificate.boundaryCarry + " to the prefix integer and leaves remainder " + certificate.canonicalRemainder + ". The finite integer identity has been checked exactly.");
  const localCount = (3n * row.remainder) / 997n;
  put("local-equation", "3 × " + row.remainder + " = " + (3n * row.remainder));
  put("local-word", word(row.word));
  put("local-addition", row.remainder + " + " + localCount);
  put("local-remainder", row.nextRemainder);
  drawSplit(0);
  put("orbit-position", "Group " + (selected + 1) + " · " + (selected < 166 ? "first" : "second") + " trip around");
  put("orbit-power", compact(row.raw));
  put("power-size", "3" + superscript(selected) + " · " + row.raw.toString().length + (row.raw.toString().length === 1 ? " digit" : " digits"));
  put("orbit-remainder", row.remainder);
  element("remainder-dot").style.left = (Number(row.remainder) / 996 * 100) + "%";
  element<HTMLButtonElement>("cycle-later").disabled = selected >= 166;
  element("cycle-earlier").hidden = selected < 166;
  put("whole-power", "3" + superscript(selected) + " = " + row.raw);
  const partner = selected < 166 ? selected + 166 : selected - 166;
  put("cycle-message", "Groups " + (Math.min(selected, partner) + 1) + " and " + (Math.max(selected, partner) + 1) + " have the same remainder, " + row.remainder + ", and print the same group, " + word(row.word) + ". Their growing powers are 166 multiplications apart.");
  if (message) announce(message + " Group " + (selected + 1) + ", printed " + word(row.word) + ", remainder " + row.remainder + ".");
}

function select(index: number, message: string): void {
  selected = Math.min(331, Math.max(0, Math.trunc(index)));
  render(message);
  rememberPosition();
}

window.addEventListener("popstate", () => {
  const fromURL = positionFromSearch(window.location.search);
  selected = fromURL ?? 6;
  if (fromURL !== null) revealed = true;
  renderReveal();
  render("Restored the linked position.");
});

element("share-position").addEventListener("click", async () => {
  const index = selected;
  const url = linkToPosition(index);
  try {
    if (!navigator.clipboard?.writeText) throw new Error("Clipboard unavailable");
    await navigator.clipboard.writeText(url);
    put("share-position", "Link copied");
    put("share-help", "Copied a link to group " + (index + 1) + ".");
    announce("Link to group " + (index + 1) + " copied.");
  } catch {
    const field = element<HTMLInputElement>("share-link");
    field.value = url;
    element("share-link-label").hidden = false;
    put("share-help", "Select and copy this link to group " + (index + 1) + ".");
    field.focus({ preventScroll: true });
    field.select();
    announce("The link to group " + (index + 1) + " is selected. Copy it using your browser or keyboard.");
  }
});

element("previous").addEventListener("click", () => select(selected - 1, "Previous group."));
element("next").addEventListener("click", () => select(selected + 1, "Next group."));
element("reset").addEventListener("click", () => select(6, "Back to the first change."));
element<HTMLInputElement>("position").addEventListener("input", event => select(Number((event.target as HTMLInputElement).value), "Selected."));
element("cycle-later").addEventListener("click", () => {
  if (selected < 166) {
    select(selected + 166, "One cycle later. The remainder and printed group return.");
    element("cycle-earlier").focus({ preventScroll: true });
  }
});
element("cycle-earlier").addEventListener("click", () => {
  if (selected >= 166) {
    select(selected - 166, "One cycle earlier.");
    element("cycle-later").focus({ preventScroll: true });
  }
});
element("reveal").addEventListener("click", () => {
  if (revealed) {
    element("carry").scrollIntoView({ behavior: reducedMotion.matches ? "instant" : "smooth" });
    element("next").focus({ preventScroll: true });
    return;
  }
  revealed = true;
  renderReveal();
  select(6, "The next group is 731, although the next power of three is 729.");
});
element("animate-split").addEventListener("click", () => {
  if (animationFrame) return;
  if (reducedMotion.matches) {
    drawSplit(1);
    announce("Split complete. " + element("split-svg").getAttribute("aria-label"));
    return;
  }
  const began = performance.now();
  element("animate-split").setAttribute("aria-disabled", "true");
  function tick(now: number): void {
    const fraction = Math.min(1, (now - began) / 950);
    drawSplit(1 - (1 - fraction) ** 3);
    if (fraction < 1) animationFrame = requestAnimationFrame(tick);
    else {
      stopAnimation();
      announce("Split complete. " + element("split-svg").getAttribute("aria-label"));
    }
  }
  animationFrame = requestAnimationFrame(tick);
});
reducedMotion.addEventListener("change", () => {
  if (reducedMotion.matches && animationFrame) { stopAnimation(); drawSplit(1); }
});

initGeometry(element("geometry-app"));
render();
renderReveal();
document.documentElement.classList.add("js");
