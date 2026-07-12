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

/-- Minimal layout fixes for FABL's long title and joined statement/code cards in
the official Blueprint theme. -/
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
"#⟩

/-- HTML configuration for FABL's book-and-code layout. -/
def fablRenderConfig : RenderConfig :=
  let config : RenderConfig := {}
  let htmlConfig := config.toHtmlConfig
  let htmlAssets := htmlConfig.toHtmlAssets
  { config with
    toHtmlConfig := { htmlConfig with
      toHtmlAssets := {
        htmlAssets with
        extraCss := htmlAssets.extraCss.insert statementCodeLayoutCss
      }
    }
  }

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc FABLBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := fablRenderConfig)
