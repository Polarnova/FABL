import VersoManual
import VersoBlueprint.PreviewManifest
import FABLBlueprint.Book

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc FABLBlueprint.Book)
    args
    (extensionImpls := by exact extension_impls%)
