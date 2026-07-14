/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import FABLBlueprint.Chapter01
import FABLBlueprint.Chapter02
import FABLBlueprint.Chapter03
import FABLBlueprint.Chapter04

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option maxRecDepth 4096

#doc (Manual) "Analysis of Boolean Functions in Lean" =>

FABL formalizes the May 2021 edition of
[Ryan O'Donnell's *Analysis of Boolean Functions*](https://arxiv.org/abs/2105.10386)
in Lean 4 and Mathlib. The present volume covers Chapters 1--4.

Each entry gives the book-facing statement and its associated Lean declarations.
The graph below records the mathematical dependencies between results.

{include 0 FABLBlueprint.Chapter01}
{include 0 FABLBlueprint.Chapter02}
{include 0 FABLBlueprint.Chapter03}
{include 0 FABLBlueprint.Chapter04}

{blueprint_graph}
