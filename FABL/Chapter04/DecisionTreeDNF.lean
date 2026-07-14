/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Grok 4.5
-/
module

public import FABL.Chapter03.SubspacesAndDecisionTrees
public import FABL.Chapter04.DNFFormulas

/-!
# Decision trees to DNF/CNF (Proposition 4.5)

Book items: Proposition 4.5, Example 4.6.

Converts a decision tree of size `s` and depth `k` into a DNF (and CNF) of size at most `s`
and width at most `k`, by taking one term per True leaf path (respectively one clause per False
leaf path).
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Cube bridge: binary decision trees vs sign-cube Boolean functions -/

/-- Pull a binary-cube Boolean function back to the sign cube via the standard equivalence. -/
def booleanFunctionOfBinary (f : 𝔽₂^[n] → Sign) : BooleanFunction n :=
  fun x ↦ f ((binaryCubeSignEquiv n).symm x)

/-- Push a sign-cube Boolean function forward to the binary cube. -/
def binaryOfBooleanFunction (f : BooleanFunction n) : 𝔽₂^[n] → Sign :=
  fun x ↦ f (binaryCubeSignEquiv n x)

@[simp] theorem booleanFunctionOfBinary_binaryOfBooleanFunction (f : BooleanFunction n) :
    booleanFunctionOfBinary (binaryOfBooleanFunction f) = f := by
  funext x
  simp [booleanFunctionOfBinary, binaryOfBooleanFunction]

@[simp] theorem binaryOfBooleanFunction_booleanFunctionOfBinary (f : 𝔽₂^[n] → Sign) :
    binaryOfBooleanFunction (booleanFunctionOfBinary f) = f := by
  funext x
  simp [booleanFunctionOfBinary, binaryOfBooleanFunction]

/-! ## Paths to DNF terms -/

namespace F₂DecisionTree.Path

/-- Required sign forced by a path on a support coordinate. -/
noncomputable def requiredSign (path : Path n Sign) (i : Fin n) (hi : i ∈ path.support) : Sign := by
  classical
  have h : path.assignment i ≠ none := (Path.mem_support path i).1 hi
  exact signEncode ((path.assignment i).get (Option.ne_none_iff_isSome.mp h))

theorem requiredSign_spec (path : Path n Sign) (i : Fin n) (hi : i ∈ path.support)
    {b : 𝔽₂} (hb : path.assignment i = some b) :
    path.requiredSign i hi = signEncode b := by
  classical
  simp only [requiredSign]
  -- `get` of `some b` is `b`
  have hsome : path.assignment i = some b := hb
  simp [hsome, Option.get_some]

/-- Literals of a path as a list, one per queried coordinate. -/
noncomputable def toLiterals (path : Path n Sign) : List (Literal n) := by
  classical
  exact path.support.attach.toList.map fun ⟨i, hi⟩ ↦ ⟨i, path.requiredSign i hi⟩

theorem toLiterals_nodupIndices (path : Path n Sign) :
    (path.toLiterals.map Literal.index).Nodup := by
  classical
  -- Indices are the support elements, which are distinct.
  have hmap :
      path.toLiterals.map Literal.index =
        path.support.attach.toList.map (fun p : {i // i ∈ path.support} ↦ (p : Fin n)) := by
    simp only [toLiterals, List.map_map]
    rfl
  rw [hmap]
  have hnodup : path.support.attach.toList.Nodup := path.support.attach.nodup_toList
  refine (List.nodup_map_iff_inj_on hnodup).2 ?_
  intro a _ha b _hb hab
  exact Subtype.ext hab

/-- DNF term associated to a path (used for True leaves). -/
noncomputable def toDNFTerm (path : Path n Sign) : DNFTerm n where
  literals := path.toLiterals
  nodupIndices := path.toLiterals_nodupIndices

theorem width_toDNFTerm (path : Path n Sign) :
    path.toDNFTerm.width = path.length := by
  classical
  simp only [toDNFTerm, DNFTerm.width, toLiterals, length, List.length_map,
    Finset.length_toList, Finset.card_attach]

theorem eval_toDNFTerm_eq_neg_one_iff (path : Path n Sign) (x : {−1,1}^[n]) :
    path.toDNFTerm.eval x = -1 ↔
      path.Matches ((binaryCubeSignEquiv n).symm x) := by
  classical
  rw [DNFTerm.eval_eq_neg_one_iff]
  constructor
  · intro h i b hib
    have hi : i ∈ path.support := (Path.mem_support path i).2 (by simp [hib])
    have hℓ : (⟨i, path.requiredSign i hi⟩ : Literal n) ∈ path.toLiterals := by
      simp only [toLiterals, List.mem_map, Finset.mem_toList]
      exact ⟨⟨i, hi⟩, by simp, rfl⟩
    have hx : x i = path.requiredSign i hi := by
      simpa using h _ hℓ
    have hr : path.requiredSign i hi = signEncode b := path.requiredSign_spec i hi hib
    have hx' : x i = signEncode b := hx.trans hr
    -- binaryCubeSignEquiv applies coordinatewise signEncode
    have happly :
        signEncode (((binaryCubeSignEquiv n).symm x) i) = x i :=
      congrFun (Equiv.apply_symm_apply (binaryCubeSignEquiv n) x) i
    have hsym : signEncode (((binaryCubeSignEquiv n).symm x) i) = signEncode b :=
      happly.trans hx'
    exact binarySignEquiv.injective hsym
  · intro hMatches ℓ hℓ
    simp only [toDNFTerm, toLiterals, List.mem_map, Finset.mem_toList] at hℓ
    rcases hℓ with ⟨⟨i, hi⟩, _, rfl⟩
    have hassign : ∃ b, path.assignment i = some b := by
      have : path.assignment i ≠ none := (Path.mem_support path i).1 hi
      exact Option.ne_none_iff_exists'.mp this
    rcases hassign with ⟨b, hb⟩
    have hbin : ((binaryCubeSignEquiv n).symm x) i = b := hMatches i b hb
    have hr : path.requiredSign i hi = signEncode b := path.requiredSign_spec i hi hb
    have happly :
        signEncode (((binaryCubeSignEquiv n).symm x) i) = x i :=
      congrFun (Equiv.apply_symm_apply (binaryCubeSignEquiv n) x) i
    have : x i = signEncode b := by
      rw [hbin] at happly
      exact happly.symm
    simpa [hr] using this

end F₂DecisionTree.Path

/-! ## Proposition 4.5: decision tree → DNF -/

namespace F₂DecisionTree

/-- DNF obtained by taking one term per True leaf path. -/
noncomputable def toDNFFormula {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) : DNFFormula n where
  terms := (T.paths.filter fun path ↦ decide (path.output = (-1 : Sign))).map Path.toDNFTerm

theorem size_toDNFFormula_le {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) :
    T.toDNFFormula.size ≤ T.leafCount := by
  classical
  simp only [toDNFFormula, DNFFormula.size, List.length_map]
  have := List.length_filter_le
    (fun path : Path n Sign ↦ decide (path.output = (-1 : Sign))) T.paths
  exact this.trans_eq T.length_paths_eq_leafCount

theorem width_toDNFFormula_le {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) :
    T.toDNFFormula.width ≤ T.depth := by
  classical
  rw [DNFFormula.width_le_iff]
  intro term hterm
  simp only [toDNFFormula, List.mem_map, List.mem_filter] at hterm
  rcases hterm with ⟨path, ⟨hpath, _⟩, rfl⟩
  have hlen : path.length ≤ T.depth := path_length_le_depth T path hpath
  simpa [Path.width_toDNFTerm] using hlen

theorem eval_toDNFFormula {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) (x : {−1,1}^[n]) :
    T.toDNFFormula.eval x = -1 ↔
      ∃ path ∈ T.paths, path.output = (-1 : Sign) ∧
        path.Matches ((binaryCubeSignEquiv n).symm x) := by
  classical
  rw [DNFFormula.eval_eq_neg_one_iff]
  constructor
  · rintro ⟨term, hterm, hTx⟩
    simp only [toDNFFormula, List.mem_map, List.mem_filter, decide_eq_true_eq] at hterm
    rcases hterm with ⟨path, ⟨hpath, hout⟩, rfl⟩
    exact ⟨path, hpath, hout, (Path.eval_toDNFTerm_eq_neg_one_iff path x).1 hTx⟩
  · rintro ⟨path, hpath, hout, hmatch⟩
    refine ⟨path.toDNFTerm, ?_, (Path.eval_toDNFTerm_eq_neg_one_iff path x).2 hmatch⟩
    simp only [toDNFFormula, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨path, ⟨hpath, hout⟩, rfl⟩

/-- Evaluation of the DNF agrees with the tree on the sign cube. -/
theorem toDNFFormula_toBooleanFunction {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) :
    T.toDNFFormula.toBooleanFunction =
      booleanFunctionOfBinary T.eval := by
  classical
  funext x
  change T.toDNFFormula.eval x = T.eval ((binaryCubeSignEquiv n).symm x)
  -- Tree value is the unique matching path's output.
  obtain ⟨path, hpathMatch, huniq⟩ :=
    existsUnique_path_mem_and_matches T ((binaryCubeSignEquiv n).symm x)
  obtain ⟨hpath, hmatch⟩ := hpathMatch
  have hval : T.eval ((binaryCubeSignEquiv n).symm x) = path.output :=
    eval_eq_path_output_of_mem_of_matches T path _ hpath hmatch
  rcases Int.units_eq_one_or path.output with hout | hout
  · -- False leaf: no True path matches, so DNF is False (= 1)
    have hnone : ¬ ∃ p ∈ T.paths, p.output = (-1 : Sign) ∧
        p.Matches ((binaryCubeSignEquiv n).symm x) := by
      rintro ⟨p, hp, hpo, hpm⟩
      have : p = path := huniq p ⟨hp, hpm⟩
      subst p
      simp [hout] at hpo
    have hDNF : T.toDNFFormula.eval x ≠ -1 := by
      intro h
      exact hnone ((eval_toDNFFormula T x).1 h)
    have : T.toDNFFormula.eval x = 1 := by
      rcases Int.units_eq_one_or (T.toDNFFormula.eval x) with h1 | hneg
      · exact h1
      · exact absurd hneg hDNF
    simp [this, hval, hout]
  · -- True leaf: the matching path gives a True term
    have hex : ∃ p ∈ T.paths, p.output = (-1 : Sign) ∧
        p.Matches ((binaryCubeSignEquiv n).symm x) :=
      ⟨path, hpath, hout, hmatch⟩
    have hDNF : T.toDNFFormula.eval x = -1 := (eval_toDNFFormula T x).2 hex
    simp [hDNF, hval, hout]

/-- O'Donnell, Proposition 4.5 (DNF form): a decision tree of size `s` and depth `k` yields a
DNF of size at most `s` and width at most `k`. -/
theorem hasDNFSizeWidth_of_decisionTree {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) :
    HasDNFSizeLE (booleanFunctionOfBinary T.eval) T.leafCount ∧
      HasDNFWidthLE (booleanFunctionOfBinary T.eval) T.depth := by
  refine ⟨
    ⟨T.toDNFFormula, T.size_toDNFFormula_le, T.toDNFFormula_toBooleanFunction⟩,
    ⟨T.toDNFFormula, T.width_toDNFFormula_le, T.toDNFFormula_toBooleanFunction⟩⟩

/-- O'Donnell, Proposition 4.5 for a complete available-coordinate tree computing a Boolean
function on the sign cube. -/
theorem hasDNFSizeWidth_of_computes
    (T : DecisionTree n Sign) (f : BooleanFunction n)
    (hT : T.Computes (binaryOfBooleanFunction f)) :
    HasDNFSizeLE f T.leafCount ∧ HasDNFWidthLE f T.depth := by
  have h := T.hasDNFSizeWidth_of_decisionTree
  -- booleanFunctionOfBinary T.eval = f
  have heq : booleanFunctionOfBinary T.eval = f := by
    funext x
    -- hT : T.eval = binaryOfBooleanFunction f
    have hx := congrFun hT ((binaryCubeSignEquiv n).symm x)
    -- hx : T.eval (symm x) = f x after simplifying binaryOfBooleanFunction
    exact hx.trans (by simp [binaryOfBooleanFunction])
  simpa [heq] using h

/-! ## CNF form of Proposition 4.5 -/

/-- CNF obtained by taking one clause per False leaf path (dual construction). -/
noncomputable def toCNFFormula {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) : CNFFormula n where
  clauses := (T.paths.filter fun path ↦ decide (path.output = (1 : Sign))).map Path.toDNFTerm

theorem size_toCNFFormula_le {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) :
    T.toCNFFormula.size ≤ T.leafCount := by
  classical
  simp only [toCNFFormula, CNFFormula.size, List.length_map]
  have := List.length_filter_le
    (fun path : Path n Sign ↦ decide (path.output = (1 : Sign))) T.paths
  exact this.trans_eq T.length_paths_eq_leafCount

theorem width_toCNFFormula_le {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) :
    T.toCNFFormula.width ≤ T.depth := by
  classical
  -- width of CNF is width of the clause list as a DNF formula
  change (DNFFormula.mk T.toCNFFormula.clauses).width ≤ T.depth
  rw [DNFFormula.width_le_iff]
  intro term hterm
  simp only [toCNFFormula, List.mem_map, List.mem_filter] at hterm
  rcases hterm with ⟨path, ⟨hpath, _⟩, rfl⟩
  have hlen : path.length ≤ T.depth := path_length_le_depth T path hpath
  simpa [Path.width_toDNFTerm] using hlen

end F₂DecisionTree

/-- O'Donnell, Proposition 4.5 (existential form). -/
theorem exists_DNF_of_decisionTree
    (f : BooleanFunction n) (s k : ℕ)
    (T : DecisionTree n Sign)
    (hT : T.Computes (binaryOfBooleanFunction f))
    (hs : T.leafCount ≤ s) (hk : T.depth ≤ k) :
    HasDNFSizeLE f s ∧ HasDNFWidthLE f k := by
  obtain ⟨hsize, hwidth⟩ := F₂DecisionTree.hasDNFSizeWidth_of_computes T f hT
  constructor
  · obtain ⟨φ, hφs, hφ⟩ := hsize
    exact ⟨φ, hφs.trans hs, hφ⟩
  · obtain ⟨φ, hφw, hφ⟩ := hwidth
    exact ⟨φ, hφw.trans hk, hφ⟩

end FABL
