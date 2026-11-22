import { renderPowerFamily, renderRegrouping } from "./power-dial-view.ts";
import { powerFamily, regroup997 } from "./math/power-dial.ts";

export function initPowerDial(): void {
  const chapter = document.getElementById("power-and-grouping");
  if (!chapter) return;
  const get = <T extends HTMLElement>(id: string) => document.getElementById(id) as T;
  const powerSlider = get<HTMLInputElement>("power-width");
  const groupSlider = get<HTMLInputElement>("group-width");
  let width = 3;
  let groupWidth = 3;
  let revealed = false;
  const validWidth = (raw: string | null, min: number) => {
    const n = Number(raw ?? 3);
    return Number.isInteger(n) && n >= min && n <= 6 ? n : 3;
  };
  const readURL = () => {
    const params = new URLSearchParams(location.search);
    width = validWidth(params.get("power_width"), 2);
    groupWidth = validWidth(params.get("group_width"), 3);
    revealed = params.get("power_reveal") === "1";
  };
  const remember = () => {
    if (!/^https?:$/.test(location.protocol)) return;
    const url = new URL(location.href);
    url.searchParams.set("power_width", String(width));
    url.searchParams.set("group_width", String(groupWidth));
    if (revealed) url.searchParams.set("power_reveal", "1");
    else url.searchParams.delete("power_reveal");
    try { history.replaceState(null, "", url); } catch { /* Controls also work in restricted previews. */ }
  };
  const renderAnswer = () => {
    get("power-answer").hidden = !revealed;
    get("power-reveal").setAttribute("aria-expanded", String(revealed));
    get("power-reveal").textContent = revealed ? "Hide the answer" : "Check the next group";
  };
  const renderPower = (announce = false) => {
    powerSlider.value = String(width);
    powerSlider.setAttribute("aria-valuetext", `10 to the power ${width}; ${width}-digit boxes; denominator ${10 ** width - 3}`);
    get("power-width-label").textContent = `10${"⁰¹²³⁴⁵⁶"[width]} · ${width}-digit boxes`;
    get("power-result").innerHTML = renderPowerFamily(width);
    chapter.querySelectorAll<HTMLButtonElement>("[data-power-width]").forEach(b => b.setAttribute("aria-pressed", String(Number(b.dataset.powerWidth) === width)));
    renderAnswer();
    if (announce) {
      const p = powerFamily(width);
      get("power-status").textContent = `1/${p.denominator}, ${width}-digit boxes. ${p.cleanCount} unchanged opening groups. ${p.field.count} integer field members; square-root width exactly one. The next group is ready to check.`;
    }
  };
  const renderGroup = (announce = false) => {
    groupSlider.value = String(groupWidth);
    groupSlider.setAttribute("aria-valuetext", `${groupWidth}-digit boxes; fraction one over 997`);
    get("group-width-label").textContent = String(groupWidth);
    get("group-result").innerHTML = renderRegrouping(groupWidth);
    chapter.querySelectorAll<HTMLButtonElement>("[data-group-width]").forEach(b => b.setAttribute("aria-pressed", String(Number(b.dataset.groupWidth) === groupWidth)));
    if (announce) {
      const p = regroup997(groupWidth);
      get("group-status").textContent = `1/997, ${groupWidth}-digit boxes. Start with ${p.quotient}, multiply by ${p.remainder}. ${p.cleanCount} unchanged groups. The sixty decimal digits are unchanged.`;
    }
  };
  const setPower = (value: number, announce = true) => { width = value; revealed = false; renderPower(announce); remember(); };
  const setGroup = (value: number, announce = true) => { groupWidth = value; renderGroup(announce); remember(); };
  powerSlider.addEventListener("input", () => setPower(Number(powerSlider.value), false));
  powerSlider.addEventListener("change", () => renderPower(true));
  groupSlider.addEventListener("input", () => setGroup(Number(groupSlider.value), false));
  groupSlider.addEventListener("change", () => renderGroup(true));
  chapter.querySelectorAll<HTMLButtonElement>("[data-power-width]").forEach(b => b.addEventListener("click", () => setPower(Number(b.dataset.powerWidth))));
  chapter.querySelectorAll<HTMLButtonElement>("[data-group-width]").forEach(b => b.addEventListener("click", () => setGroup(Number(b.dataset.groupWidth))));
  get("power-result").addEventListener("click", event => {
    if (!(event.target instanceof Element) || !event.target.closest("#power-reveal")) return;
    revealed = !revealed;
    renderAnswer();
    remember();
    const p = powerFamily(width);
    get("power-status").textContent = revealed ? `Group ${p.firstChangedPosition}: ${p.expected} plus incoming carry ${p.carry} prints ${p.actual}.` : "Answer hidden.";
  });
  window.addEventListener("popstate", () => { readURL(); renderPower(); renderGroup(); });
  readURL();
  renderPower();
  renderGroup();
}
