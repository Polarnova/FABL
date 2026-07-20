/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter01.FunctionsAsMultilinearPolynomials

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "On analysis of Boolean functions" =>

:::definition "support-hamming-cube" (parent := "fabl-chapter-1") (lean := "FABL.SignCube, FABL.F₂Cube, hammingDist") (tags := "section-1-1, support")
*Section 1.1.* The sign representation of the Hamming cube is
$`\{-1,1\}^n`, and its additive representation is $`\mathbb F_2^n`. For two
strings $`x` and $`y` in a common product, their Hamming distance is
$`\Delta(x,y)=\#\{i:x_i\ne y_i\},`
the number of coordinates at which they differ.
:::
