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
import FABLBlueprint.Chapter05

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option maxRecDepth 4096

#doc (Manual) "Analysis of Boolean Functions in Lean" =>

This Blueprint follows the May 2021 edition of
[Ryan O'Donnell's *Analysis of Boolean Functions*](https://arxiv.org/abs/2105.10386)
and uses its ordering and notation.

The graph below records the mathematical dependencies among the definitions
and results.

:::group "fabl-chapter-1"
Chapter 1: Boolean functions and the Fourier expansion
:::

:::group "fabl-chapter-2"
Chapter 2: Influence and noise sensitivity
:::

:::group "fabl-chapter-3"
Chapter 3: Spectral structure and learning
:::

:::group "fabl-chapter-4"
Chapter 4: DNF formulas and small-depth circuits
:::

:::group "fabl-chapter-5"
Chapter 5: Majority and threshold functions
:::

{include 0 FABLBlueprint.Chapter01}
{include 0 FABLBlueprint.Chapter02}
{include 0 FABLBlueprint.Chapter03}
{include 0 FABLBlueprint.Chapter04}
{include 0 FABLBlueprint.Chapter05}

{blueprint_graph (direction := LR)}
