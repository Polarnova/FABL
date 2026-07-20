/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import VersoManual
import VersoBlueprint.PreviewManifest
import FABLBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

/-- Reader-facing layout and metadata controls for the official Blueprint theme. -/
def statementCodeLayoutCss : CSS := ⟨r#"
@media screen and (min-width: 701px) {
  html[data-bp-style="blueprint"] .header-title-wrapper {
    box-sizing: border-box;
    min-width: 0;
    padding-right: calc(var(--search-bar-width) + 1rem);
  }

  html[data-bp-style="blueprint"] .header-title {
    font-size: clamp(1rem, 1.4vw, 1.5rem);
    overflow: hidden;
    text-overflow: ellipsis;
  }
}

html[data-bp-style="blueprint"]
  .bp_wrapper[id$="--statement"]:has(+ .bp_code_panel_wrapper) {
  margin-bottom: 0;
  border-bottom: 0;
  border-bottom-left-radius: 0;
  border-bottom-right-radius: 0;
}

html[data-bp-style="blueprint"]
  .bp_wrapper[id$="--statement"] + .bp_code_panel_wrapper {
  margin-top: 0;
  border-top-left-radius: 0;
  border-top-right-radius: 0;
}

.bp_external_decl_header_status.bp_external_decl_ok,
.bp_code_decl_status.bp_code_decl_status_ok {
  display: none;
}

html:not([data-fabl-tags-ready]) .bp_metadata_tags {
  visibility: hidden;
}

html[data-fabl-fidelity="hidden"] .fabl-fidelity-tag {
  display: none;
}

#bp-style-switcher .fabl-fidelity-control input {
  margin: 0;
}

a.bp_external_decl_source_path {
  text-decoration-thickness: from-font;
  text-underline-offset: 0.12rem;
}
"#⟩

private def blueprintReaderJsTemplate : String := r#"
(function () {
  "use strict";

  const fidelityStorageKey = "fabl-blueprint-show-fidelity";
  const repositories = [
    {
      prefix: "FABL/",
      sourceRoot: "https://github.com/Polarnova/FABL/blob/__FABL_REVISION__/"
    },
    {
      prefix: "ProbabilityApproximation/",
      sourceRoot:
        "https://github.com/Polarnova/ProbabilityApproximation/blob/__PROBABILITY_REVISION__/"
    },
    {
      prefix: "Mathlib/",
      sourceRoot:
        "https://github.com/leanprover-community/mathlib4/blob/__MATHLIB_REVISION__/"
    }
  ];

  function savedFidelityVisibility() {
    try {
      return localStorage.getItem(fidelityStorageKey) === "shown";
    } catch (_error) {
      return false;
    }
  }

  function setFidelityVisibility(shown, persist) {
    const root = document.documentElement;
    if (!root) return;
    root.setAttribute("data-fabl-fidelity", shown ? "shown" : "hidden");
    const input = document.getElementById("fabl-fidelity-toggle");
    if (input instanceof HTMLInputElement) input.checked = shown;
    if (!persist) return;
    try {
      localStorage.setItem(fidelityStorageKey, shown ? "shown" : "hidden");
    } catch (_error) {}
  }

  function classifyFidelityTags() {
    document.querySelectorAll(".bp_metadata_tag").forEach(function (tag) {
      if ((tag.textContent || "").trim().startsWith("fidelity-")) {
        tag.classList.add("fabl-fidelity-tag");
      }
    });
    document.documentElement.setAttribute("data-fabl-tags-ready", "true");
  }

  function collapseCodePanels() {
    document.querySelectorAll("details.bp_code_panel[open]").forEach(function (panel) {
      panel.removeAttribute("open");
    });
  }

  function installFidelityControl() {
    if (document.getElementById("fabl-fidelity-toggle")) return true;
    const host = document.getElementById("bp-style-switcher");
    if (!host) return false;

    const control = document.createElement("div");
    control.className = "bp-style-switcher-control fabl-fidelity-control";

    const input = document.createElement("input");
    input.id = "fabl-fidelity-toggle";
    input.type = "checkbox";
    input.checked =
      document.documentElement.getAttribute("data-fabl-fidelity") === "shown";

    const label = document.createElement("label");
    label.setAttribute("for", input.id);
    label.textContent = "Fidelity tags";

    input.addEventListener("change", function () {
      setFidelityVisibility(input.checked, true);
    });

    control.appendChild(input);
    control.appendChild(label);
    host.appendChild(control);
    return true;
  }

  function installFidelityControlWhenReady() {
    if (installFidelityControl()) return;
    const observer = new MutationObserver(function () {
      if (installFidelityControl()) observer.disconnect();
    });
    observer.observe(document.body, { childList: true, subtree: true });
    window.setTimeout(function () {
      observer.disconnect();
    }, 5000);
  }

  function encodedSourcePath(path) {
    return path.split("/").map(encodeURIComponent).join("/");
  }

  function sourceRootFor(path) {
    return repositories.find(function (repository) {
      return path.startsWith(repository.prefix);
    });
  }

  function declarationRanges(manifest) {
    const ranges = new Map();
    if (!manifest || !Array.isArray(manifest.previews)) return ranges;
    manifest.previews.forEach(function (preview) {
      const declarations =
        preview && preview.codeData && preview.codeData.external
          ? preview.codeData.external.decls
          : null;
      if (!Array.isArray(declarations)) return;
      declarations.forEach(function (declaration) {
        if (declaration && declaration.canonical) {
          ranges.set(declaration.canonical, declaration.range || null);
        }
      });
    });
    return ranges;
  }

  function sourceAnchor(range) {
    if (!range || !Array.isArray(range.pos) || !Array.isArray(range.endPos)) {
      return { fragment: "", suffix: "" };
    }
    const start = Number(range.pos[0]) + 1;
    const end = Number(range.endPos[0]) + 1;
    if (!Number.isFinite(start) || !Number.isFinite(end)) {
      return { fragment: "", suffix: "" };
    }
    return {
      fragment: end > start ? "#L" + start + "-L" + end : "#L" + start,
      suffix: ":L" + start
    };
  }

  function linkDeclarationSources(ranges) {
    document
      .querySelectorAll(".bp_external_decl_rendered .declaration[data-decl]")
      .forEach(function (declaration) {
        const source = declaration.querySelector(".bp_external_decl_source_path");
        if (!source || source instanceof HTMLAnchorElement) return;
        const path = (source.textContent || "").trim();
        const repository = sourceRootFor(path);
        if (!repository) return;

        const canonical = declaration.getAttribute("data-decl") || "";
        const anchor = sourceAnchor(ranges.get(canonical));
        const link = document.createElement("a");
        link.className = source.className;
        link.href =
          repository.sourceRoot + encodedSourcePath(path) + anchor.fragment;
        link.textContent = path + anchor.suffix;
        link.target = "_blank";
        link.rel = "noopener noreferrer";
        link.title = "Open this declaration in its source repository";
        source.replaceWith(link);
      });
  }

  async function installSourceLinks() {
    try {
      const manifestUrl = new URL(
        "-verso-data/blueprint-manifest.json",
        document.baseURI
      );
      const response = await fetch(manifestUrl);
      if (!response.ok) return;
      linkDeclarationSources(declarationRanges(await response.json()));
    } catch (_error) {}
  }

  setFidelityVisibility(savedFidelityVisibility(), false);
  document.addEventListener("DOMContentLoaded", function () {
    setFidelityVisibility(savedFidelityVisibility(), false);
    collapseCodePanels();
    classifyFidelityTags();
    installSourceLinks();
    installFidelityControlWhenReady();
  });
})();
"#

private def blueprintReaderJs
    (fablRevision probabilityRevision mathlibRevision : String) : JS :=
  ⟨blueprintReaderJsTemplate
    |>.replace "__FABL_REVISION__" fablRevision
    |>.replace "__PROBABILITY_REVISION__" probabilityRevision
    |>.replace "__MATHLIB_REVISION__" mathlibRevision⟩

/-- HTML configuration for FABL's book-and-code layout. -/
def fablRenderConfig (readerJs : JS) : RenderConfig :=
  let config : RenderConfig := {}
  let htmlConfig := config.toHtmlConfig
  let htmlAssets := htmlConfig.toHtmlAssets
  { config with
    toHtmlConfig := { htmlConfig with
      toHtmlAssets := {
        htmlAssets with
        extraCss := htmlAssets.extraCss.insert statementCodeLayoutCss
        extraJs := htmlAssets.extraJs.insert readerJs
      }
    }
  }

private def sourceRevision (variable fallback : String) : IO String := do
  return (← IO.getEnv variable).getD fallback

def main (args : List String) : IO UInt32 := do
  let fablRevision ← sourceRevision "FABL_SOURCE_REVISION" "main"
  let probabilityRevision ←
    sourceRevision "PROBABILITY_APPROXIMATION_SOURCE_REVISION" "v0.9.5"
  let mathlibRevision ← sourceRevision "MATHLIB_SOURCE_REVISION" "v4.32.0"
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc FABLBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := fablRenderConfig <|
      blueprintReaderJs fablRevision probabilityRevision mathlibRevision)
