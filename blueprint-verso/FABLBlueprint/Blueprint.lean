import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import FABLBlueprint.Chapter01
import FABLBlueprint.Commands.Summary

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Analysis of Boolean Functions in Lean" =>

This generated Blueprint renders complete book-facing statements alongside
compiled FABL declarations. Reviewed `uses` edges form the mathematical
dependency graph; Lean elaboration supplies declaration status and source
metadata. Proofs live only in the production Lean library, so the project
summary suppresses Verso's generic audit for missing prose proof blocks.

{include 0 FABLBlueprint.Chapter01}

{blueprint_graph}

{fabl_blueprint_summary}
