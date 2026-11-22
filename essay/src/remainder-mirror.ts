import { REPETITION_BOUNDARIES } from "./repetition-boundaries.ts";

const cycle = REPETITION_BOUNDARIES.find(example => example.denominator === 997n)!.grouped;
export const MIRROR_PAIRS = cycle.period / 2;

/** Curated base-1000 example; not a classification of arbitrary denominators. */
export function mirrorPair997(index: number) {
  if (!Number.isSafeInteger(index) || index < 0 || index >= MIRROR_PAIRS) {
    throw new RangeError("Choose one of the 83 pairs in the first grouped cycle.");
  }
  return { first: cycle.rows[index]!, second: cycle.rows[index + MIRROR_PAIRS]! };
}

export function initRemainderMirror(): void {
  const slider = document.getElementById("mirror-position") as HTMLInputElement;
  const put = (id: string, text: string) => { document.getElementById(id)!.textContent = text; };
  function render(index: number): void {
    const { first, second } = mirrorPair997(index);
    const word = (value: bigint) => String(value).padStart(3, "0");
    slider.value = String(index);
    slider.setAttribute("aria-valuetext", `Groups ${first.index + 1} and ${second.index + 1}: ${word(first.word)} plus ${word(second.word)} equals 999`);
    put("mirror-pair-label", `${index + 1} of ${MIRROR_PAIRS}`);
    put("mirror-first-position", `Group ${first.index + 1}`);
    put("mirror-second-position", `Group ${second.index + 1}`);
    put("mirror-first-remainder", String(first.remainder));
    put("mirror-second-remainder", String(second.remainder));
    put("mirror-first-word", word(first.word));
    put("mirror-second-word", word(second.word));
    put("mirror-sum", `${word(first.word)} + ${word(second.word)} = 999`);
    put("mirror-explanation", `The entering remainders ${first.remainder} and ${second.remainder} add to 997. Their printed groups add to 999. The next remainders, ${first.nextRemainder} and ${second.nextRemainder}, add to 997 again.`);
  }
  slider.addEventListener("input", () => render(Number(slider.value)));
  document.querySelectorAll<HTMLButtonElement>("[data-mirror-pair]").forEach(button => {
    button.addEventListener("click", () => render(Number(button.dataset.mirrorPair)));
  });
  render(0);
}
