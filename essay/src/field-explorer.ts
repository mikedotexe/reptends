import { renderFieldReading, renderFieldRuler } from "./field-view.ts";
import type { FieldStage } from "./field-view.ts";

export function initFieldExplorer(): void {
  const lesson = document.getElementById("field-lesson");
  if (!lesson) return;
  const get = <T extends HTMLElement>(id: string) => document.getElementById(id) as T;
  const slider = get<HTMLInputElement>("field-denominator");
  const next = get<HTMLButtonElement>("field-next");
  let stage: FieldStage = 1;
  let denominator = 997;
  const restore = () => {
    const params = new URLSearchParams(location.search);
    const n = Number(params.get("field_n") ?? 997);
    denominator = Number.isInteger(n) && n >= 968 && n <= 1033 ? n : 997;
    const requested = Number(params.get("field_step") ?? (params.has("field_n") ? 2 : 1));
    stage = requested === 2 || requested === 3 ? requested : 1;
    if (stage === 1) denominator = 997;
  };
  const render = (announce = false) => {
    lesson.dataset.stage = String(stage);
    lesson.querySelectorAll<HTMLElement>("[data-field-panel]").forEach(panel => { panel.hidden = Number(panel.dataset.fieldPanel) !== stage; });
    lesson.querySelectorAll<HTMLButtonElement>("[data-field-go]").forEach(button => { button.setAttribute("aria-pressed", String(Number(button.dataset.fieldGo) === stage)); });
    get("field-live-ruler").hidden = false;
    get("field-live-ruler").innerHTML = renderFieldRuler(denominator, stage);
    lesson.querySelector(`[data-field-panel="${stage}"] .field-static-ruler`)!.before(get("field-live-ruler"));
    get("field-inspector").hidden = stage === 1;
    slider.value = String(denominator);
    get("field-denominator-value").textContent = String(denominator);
    get("field-reading").innerHTML = renderFieldReading(denominator);
    next.textContent = stage === 1 ? "Reveal its neighbours" : stage === 2 ? "Open the square-root strip" : "Back to 997";
    get("field-step-count").textContent = `Step ${stage} of 3`;
    if (announce) get("field-status").textContent = `Step ${stage} of 3. ${stage === 1 ? "Start at 997." : stage === 2 ? "Meet the neighbours." : "The square-root strip is exactly one unit wide."} ${denominator} selected.`;
  };
  const remember = () => {
    if (!/^https?:$/.test(location.protocol)) return;
    const url = new URL(location.href);
    url.searchParams.set("field_step", String(stage));
    url.searchParams.set("field_n", String(denominator));
    try { history.replaceState(null, "", url); } catch { /* Restricted previews retain local controls. */ }
  };
  const chooseStage = (value: FieldStage) => {
    stage = value;
    if (stage === 1) denominator = 997;
    render(true);
    remember();
  };
  lesson.querySelectorAll<HTMLButtonElement>("[data-field-go]").forEach(button => button.addEventListener("click", () => chooseStage(Number(button.dataset.fieldGo) as FieldStage)));
  lesson.querySelectorAll<HTMLButtonElement>("[data-field-n]").forEach(button => button.addEventListener("click", () => {
    denominator = Number(button.dataset.fieldN);
    render(true);
    remember();
  }));
  slider.addEventListener("input", () => {
    denominator = Number(slider.value);
    render();
    remember();
  });
  slider.addEventListener("change", () => render(true));
  next.addEventListener("click", () => {
    chooseStage(stage === 3 ? 1 : (stage + 1) as FieldStage);
    const heading = lesson.querySelector<HTMLElement>(`[data-field-panel="${stage}"] h3`)!;
    heading.tabIndex = -1;
    heading.focus({ preventScroll: true });
    heading.scrollIntoView({ block: "start", behavior: "instant" });
  });
  window.addEventListener("popstate", () => { restore(); render(); });
  restore();
  render();
}
