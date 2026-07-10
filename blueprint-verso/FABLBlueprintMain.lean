import VersoManual
import VersoBlueprint.PreviewManifest
import FABLBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

/-- Join each book-facing statement to its generated Lean declaration panel in
the official Blueprint theme. -/
def statementCodeLayoutCss : CSS := ⟨r#"
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
