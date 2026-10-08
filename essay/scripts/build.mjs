import { mkdir, readFile, writeFile } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { build } from "esbuild";
import { assertPublishableHtml } from "./validate-artifact.ts";
import { renderOpeningExamples, renderPowerStack } from "./render-opening.ts";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const template = await readFile(resolve(root, "src/template.html"), "utf8");
for (const marker of ["<!-- APP_CSS -->", "<!-- APP_JS -->", "<!-- OPENING_EXAMPLES -->", "<!-- POWER_STACK -->"]) {
  if (template.split(marker).length !== 2) {
    throw new Error(`The page template must contain exactly one ${marker} marker.`);
  }
}

const common = {
  absWorkingDir: root,
  bundle: true,
  write: false,
  minify: true,
  metafile: true,
  legalComments: "inline",
};
const [javascript, stylesheet] = await Promise.all([
  build({
    ...common,
    entryPoints: ["src/main.ts"],
    outfile: "inline.js",
    platform: "browser",
    format: "iife",
    target: "es2020",
  }),
  build({
    ...common,
    entryPoints: ["src/styles.css"],
    outfile: "inline.css",
  }),
]);

for (const result of [javascript, stylesheet]) {
  if (result.outputFiles.length !== 1) {
    throw new Error("The standalone page must emit one inline script and one inline stylesheet only.");
  }
  for (const output of Object.values(result.metafile.outputs)) {
    if (output.imports.some(item => item.external)) {
      throw new Error("The standalone page cannot depend on external runtime imports.");
    }
  }
}

const script = javascript.outputFiles[0].text.replace(/<\/script/gi, "<\\/script");
const css = stylesheet.outputFiles[0].text.replace(/<\/style/gi, "<\\/style");
const html = template
  .replace("<!-- OPENING_EXAMPLES -->", () => renderOpeningExamples())
  .replace("<!-- POWER_STACK -->", () => renderPowerStack())
  .replace("<!-- APP_CSS -->", () => `<style>\n${css}\n</style>`)
  .replace("<!-- APP_JS -->", () => `<script>\n${script}\n</script>`);

assertPublishableHtml(html, css);

await mkdir(resolve(root, "dist"), { recursive: true });
const destination = resolve(root, "dist/index.html");
await writeFile(destination, html);
console.log(`Built ${destination} (${Buffer.byteLength(html).toLocaleString("en-US")} bytes; self-contained).`);
