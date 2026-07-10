import VersoBlueprint.Commands.Summary

namespace FABLBlueprint.Commands

open Lean Elab Command

open Verso Doc Elab Genre Manual in
block_extension Block.fablHtmlOnly where
  traverse _ _ _ _ := pure none
  toHtml := some <| fun _ goB _ _ content => content.mapM goB
  toTeX := some <| fun _ _ _ _ _ => pure .empty

open Verso Doc Elab Syntax in
/-- Render the official Blueprint summary while treating prose proof blocks as optional. -/
private def mkSummaryPart (stx : Syntax) (endPos : String.Pos.Raw) : PartElabM FinishedPart := do
  let titlePreview := "Blueprint Summary"
  let titleInlines ← `(inline | "Blueprint Summary")
  let expandedTitle ← #[titleInlines].mapM (elabInline ·)
  let metadata : Option (TSyntax `term) := some (← `(term| { number := false }))
  let summary ← Informal.Commands.buildSummary
  let state := Informal.Environment.informalExt.getState (← getEnv)
  let pendingInformalEntries := summary.pendingInformalEntries.filter fun item =>
    match state.data.get? item.label with
    | some blueprintNode => blueprintNode.statement.isNone
    | none => true
  let summary := { summary with pendingInformalEntries }
  let summaryBlock ←
    ``(Verso.Doc.Block.other (Informal.Commands.Block.summary $(quote summary)) #[])
  let block ← ``(Verso.Doc.Block.other Block.fablHtmlOnly #[$summaryBlock])
  pure <| FinishedPart.mk stx expandedTitle titlePreview metadata #[block] #[] endPos

open Verso Doc Elab Syntax PartElabM in
@[part_command Lean.Doc.Syntax.command]
public meta def fablBlueprintSummaryCmd : PartCommand
  | stx@`(block|command{fabl_blueprint_summary}) => do
    let endPos := stx.getTailPos?.get!
    closePartsUntil 1 endPos
    addPart (← mkSummaryPart stx endPos)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end FABLBlueprint.Commands
