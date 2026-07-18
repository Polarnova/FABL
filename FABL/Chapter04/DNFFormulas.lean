/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Grok 4.5
-/
module

public import FABL.Chapter02.TotalInfluence
public import FABL.Chapter03.LearningTheory.LowDegree
public import FABL.Chapter03.SubspacesAndDecisionTrees

/-!
# DNF and CNF formulas

Book items: Definition 4.1, Example 4.2, Definitions 4.3–4.4, Proposition 4.5,
Example 4.6, Proposition 4.7, Corollary 4.8, Proposition 4.9, Exercises 4.1–4.2,
and Exercise 3.17 support.

Formalization of Section 4.1 of O'Donnell's *Analysis of Boolean Functions*.

Representation note. The book introduces DNF syntax over `{0,1}` and then analyses
functions on `{-1,1}` with `-1 = True`. In the sign-cube formulation, a literal stores a
required sign for a coordinate. The resulting Boolean functions match the book.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Literals and terms (Definition 4.1) -/

/-- A literal: coordinate `index` must equal `required`. -/
structure Literal (n : ℕ) where
  /-- Variable coordinate of the literal. -/
  index : Fin n
  /-- Required sign for the coordinate (`-1` = unnegated True under book convention). -/
  required : Sign
  deriving DecidableEq, Repr

namespace Literal

/-- Evaluate a literal: `-1` (True) when the coordinate matches. -/
def eval (ℓ : Literal n) (x : {−1,1}^[n]) : Sign :=
  if x ℓ.index = ℓ.required then -1 else 1

@[simp] theorem eval_eq_neg_one_iff (ℓ : Literal n) (x : {−1,1}^[n]) :
    ℓ.eval x = -1 ↔ x ℓ.index = ℓ.required := by
  simp [eval]

/-- Negate a literal by flipping its required sign. -/
def negate (ℓ : Literal n) : Literal n := ⟨ℓ.index, -ℓ.required⟩

end Literal

/-- A DNF term: AND of literals on pairwise-distinct variables. -/
structure DNFTerm (n : ℕ) where
  /-- Literals in the term (AND). -/
  literals : List (Literal n)
  /-- Indices of the literals are pairwise distinct. -/
  nodupIndices : (literals.map Literal.index).Nodup

namespace DNFTerm

/-- Width of a term. -/
def width (T : DNFTerm n) : ℕ := T.literals.length

/-- Evaluate a term: `-1` iff every literal is satisfied. -/
def eval (T : DNFTerm n) (x : {−1,1}^[n]) : Sign :=
  if T.literals.all (fun ℓ ↦ ℓ.eval x = -1) then -1 else 1

theorem eval_eq_neg_one_iff (T : DNFTerm n) (x : {−1,1}^[n]) :
    T.eval x = -1 ↔ ∀ ℓ ∈ T.literals, x ℓ.index = ℓ.required := by
  simp [eval, List.all_eq_true, Literal.eval_eq_neg_one_iff]

/-- Empty term (constantly True). -/
def empty : DNFTerm n where
  literals := []
  nodupIndices := by simp

@[simp] theorem width_empty : (empty : DNFTerm n).width = 0 := rfl

@[simp] theorem eval_empty (x : {−1,1}^[n]) : (empty : DNFTerm n).eval x = -1 := by
  simp [empty, eval]

/-- Two-literal term on distinct coordinates. -/
def pair (i j : Fin n) (si sj : Sign) (hij : i ≠ j) : DNFTerm n where
  literals := [⟨i, si⟩, ⟨j, sj⟩]
  nodupIndices := by simp [hij]

@[simp] theorem width_pair (i j : Fin n) (si sj : Sign) (hij : i ≠ j) :
    (pair i j si sj hij).width = 2 := rfl

/-- Full minterm forcing every coordinate of `x`. -/
def minterm (x : {−1,1}^[n]) : DNFTerm n where
  literals := (List.finRange n).map fun i ↦ ⟨i, x i⟩
  nodupIndices := by
    simpa [List.map_map, Function.comp_def] using List.nodup_finRange n

theorem width_minterm (x : {−1,1}^[n]) : (minterm x).width = n := by
  simp [minterm, width, List.length_finRange]

theorem eval_minterm_eq_neg_one_iff (x y : {−1,1}^[n]) :
    (minterm x).eval y = -1 ↔ y = x := by
  rw [eval_eq_neg_one_iff]
  simp only [minterm, List.mem_map, List.mem_finRange, true_and]
  constructor
  · intro h
    funext i
    exact h ⟨i, x i⟩ ⟨i, rfl⟩
  · rintro rfl ℓ ⟨i, rfl⟩
    rfl

/-- Support of a term as a finset of indices. -/
def support (T : DNFTerm n) : Finset (Fin n) :=
  T.literals.map Literal.index |>.toFinset

theorem card_support (T : DNFTerm n) : T.support.card = T.width := by
  classical
  unfold support width
  rw [List.toFinset_card_of_nodup T.nodupIndices, List.length_map]

theorem width_le_dimension (T : DNFTerm n) : T.width ≤ n := by
  have h := T.support.card_le_univ
  rw [card_support] at h
  simpa [Fintype.card_fin] using h

end DNFTerm

/-! ## DNF formulas -/

/-- A DNF formula: logical OR of terms. -/
structure DNFFormula (n : ℕ) where
  /-- Terms of the DNF (OR). -/
  terms : List (DNFTerm n)

namespace DNFFormula

def size (φ : DNFFormula n) : ℕ := φ.terms.length

/-- Width: maximum term width (0 if empty). -/
def width (φ : DNFFormula n) : ℕ :=
  φ.terms.foldl (fun w T ↦ max w T.width) 0

private theorem foldl_max_le {α : Type*} (f : α → ℕ) (bound : ℕ) :
    ∀ (ts : List α) (acc : ℕ),
      (∀ a ∈ ts, f a ≤ bound) → acc ≤ bound →
        ts.foldl (fun w a ↦ max w (f a)) acc ≤ bound
  | [], _, _, hacc => hacc
  | a :: rest, acc, hts, hacc =>
    foldl_max_le f bound rest (max acc (f a))
      (fun b hb ↦ hts b (List.mem_cons_of_mem _ hb))
      (max_le hacc (hts a (List.mem_cons_self)))

private theorem le_foldl_max_aux {α : Type*} (f : α → ℕ) (acc : ℕ) :
    ∀ ts : List α, acc ≤ ts.foldl (fun w b ↦ max w (f b)) acc
  | [] => le_rfl
  | b :: rest =>
    le_trans (le_max_left acc (f b)) (le_foldl_max_aux f (max acc (f b)) rest)

private theorem le_foldl_max {α : Type*} (f : α → ℕ) :
    ∀ (ts : List α) (acc : ℕ) (a : α), a ∈ ts →
      f a ≤ ts.foldl (fun w b ↦ max w (f b)) acc
  | [], _, _, ha => by cases ha
  | b :: rest, acc, a, ha => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_trans (le_max_right acc (f a)) (le_foldl_max_aux f _ rest)
    · exact le_foldl_max f rest (max acc (f b)) a ha

theorem width_le_of_mem (φ : DNFFormula n) {T : DNFTerm n} (hT : T ∈ φ.terms) :
    T.width ≤ φ.width :=
  le_foldl_max DNFTerm.width φ.terms 0 T hT

theorem width_le_iff (φ : DNFFormula n) (w : ℕ) :
    φ.width ≤ w ↔ ∀ T ∈ φ.terms, T.width ≤ w := by
  constructor
  · intro hw T hT
    exact (width_le_of_mem φ hT).trans hw
  · intro h
    exact foldl_max_le DNFTerm.width w φ.terms 0 h (Nat.zero_le _)

def eval (φ : DNFFormula n) (x : {−1,1}^[n]) : Sign :=
  if φ.terms.any (fun T ↦ T.eval x = -1) then -1 else 1

theorem eval_eq_neg_one_iff (φ : DNFFormula n) (x : {−1,1}^[n]) :
    φ.eval x = -1 ↔ ∃ T ∈ φ.terms, T.eval x = -1 := by
  simp [eval, List.any_eq_true]

def empty : DNFFormula n := ⟨[]⟩

@[simp] theorem size_empty : (empty : DNFFormula n).size = 0 := rfl

@[simp] theorem eval_empty (x : {−1,1}^[n]) : (empty : DNFFormula n).eval x = 1 := by
  simp [empty, eval]

def toBooleanFunction (φ : DNFFormula n) : BooleanFunction n := φ.eval

/-- Delete all terms of width greater than `w`. -/
def truncateWidth (φ : DNFFormula n) (w : ℕ) : DNFFormula n :=
  ⟨φ.terms.filter fun T ↦ decide (T.width ≤ w)⟩

theorem width_truncateWidth_le (φ : DNFFormula n) (w : ℕ) :
    (φ.truncateWidth w).width ≤ w := by
  rw [width_le_iff]
  intro T hT
  have := List.mem_filter.mp hT
  exact of_decide_eq_true this.2

theorem size_truncateWidth_le (φ : DNFFormula n) (w : ℕ) :
    (φ.truncateWidth w).size ≤ φ.size :=
  List.length_filter_le _ _

end DNFFormula

/-! ## CNF formulas (Definition 4.4) -/

/-- A CNF formula: AND of clauses; each clause is an OR of the stored literals. -/
structure CNFFormula (n : ℕ) where
  /-- Clauses of the CNF (AND of ORs of the stored literals). -/
  clauses : List (DNFTerm n)

/-- Pointwise sign negation as an involution of the Boolean cube. -/
def signCubeNegEquiv (n : ℕ) : {−1,1}^[n] ≃ {−1,1}^[n] where
  toFun x i := -x i
  invFun x i := -x i
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

namespace CNFFormula

def size (ψ : CNFFormula n) : ℕ := ψ.clauses.length

def width (ψ : CNFFormula n) : ℕ := (DNFFormula.mk ψ.clauses).width

/-- Clause as OR of literals. -/
def clauseEval (C : DNFTerm n) (x : {−1,1}^[n]) : Sign :=
  if C.literals.any (fun ℓ ↦ ℓ.eval x = -1) then -1 else 1

def eval (ψ : CNFFormula n) (x : {−1,1}^[n]) : Sign :=
  if ψ.clauses.all (fun C ↦ clauseEval C x = -1) then -1 else 1

def toBooleanFunction (ψ : CNFFormula n) : BooleanFunction n := ψ.eval

/-- Boolean dual: `f†(x) = -f(-x)` (Exercise 1.8). -/
def booleanDual (f : BooleanFunction n) : BooleanFunction n :=
  fun x ↦ -f fun i ↦ -x i

/-- Two-point identity on signs. -/
theorem sign_eq_of_ne_neg (x s : Sign) (h : x ≠ -s) : x = s := by
  rcases Int.units_eq_one_or x with hx | hx <;> rcases Int.units_eq_one_or s with hs | hs <;>
    simp [hx, hs] at h ⊢

/-- Exercise 4.2: switch AND/OR, keeping the same literal lists as DNF terms. -/
def switchAndOr (ψ : CNFFormula n) : DNFFormula n := ⟨ψ.clauses⟩

/-- A clause (OR of literals) is false at `-x` iff the same literals form a true term at `x`. -/
theorem clauseEval_neg_iff_termEval (C : DNFTerm n) (x : {−1,1}^[n]) :
    clauseEval C (fun i ↦ -x i) = 1 ↔ C.eval x = -1 := by
  classical
  constructor
  · intro hclause
    have hnone : ¬ C.literals.any (fun ℓ ↦ ℓ.eval (fun i ↦ -x i) = -1) := by
      simp only [clauseEval] at hclause
      split_ifs at hclause with h
      · cases (by decide : (1 : Sign) ≠ -1) hclause.symm
      · exact h
    rw [DNFTerm.eval_eq_neg_one_iff]
    intro ℓ hℓ
    have : ℓ.eval (fun i ↦ -x i) ≠ -1 := by
      intro htrue
      exact hnone (List.any_eq_true.mpr ⟨ℓ, hℓ, by simpa using htrue⟩)
    -- ℓ false at -x means -x index ≠ required, so x index = required
    have : -x ℓ.index ≠ ℓ.required := by
      intro hreq
      exact this (by simp [Literal.eval, hreq])
    exact sign_eq_of_ne_neg (x ℓ.index) ℓ.required (by
      intro hx; exact this (by simp [hx]))
  · intro hterm
    -- All literals true at x ⇒ all false at -x ⇒ clause OR is false at -x
    have hnone : ¬ C.literals.any (fun ℓ ↦ ℓ.eval (fun i ↦ -x i) = -1) := by
      intro hany
      obtain ⟨ℓ, hℓ, htrue⟩ := List.any_eq_true.mp hany
      have hx : x ℓ.index = ℓ.required := (DNFTerm.eval_eq_neg_one_iff C x).1 hterm ℓ hℓ
      have : ℓ.eval (fun i ↦ -x i) = 1 := by
        simp only [Literal.eval, hx]
        split_ifs with hreq
        · -- hreq : -required = required, impossible
          rcases Int.units_eq_one_or ℓ.required with hr | hr <;> simp [hr] at hreq
        · rfl
      simp [this] at htrue
    simp only [clauseEval, hnone]
    rfl

/-- O'Donnell, Exercise 4.2: switching AND/OR turns a CNF for `f` into a DNF for the dual. -/
theorem switchAndOr_toBooleanFunction (ψ : CNFFormula n) :
    (switchAndOr ψ).toBooleanFunction = booleanDual ψ.toBooleanFunction := by
  classical
  funext x
  change (DNFFormula.mk ψ.clauses).eval x = -(ψ.eval (fun i ↦ -x i))
  by_cases hDNF : (DNFFormula.mk ψ.clauses).eval x = -1
  · obtain ⟨C, hC, hCx⟩ := (DNFFormula.eval_eq_neg_one_iff _ x).1 hDNF
    have hclause1 : clauseEval C (fun i ↦ -x i) = 1 := (clauseEval_neg_iff_termEval C x).2 hCx
    have hψ : ψ.eval (fun i ↦ -x i) = 1 := by
      simp only [CNFFormula.eval]
      split_ifs with hall
      · have : clauseEval C (fun i ↦ -x i) = -1 := by
          have := of_decide_eq_true (List.all_eq_true.mp hall C hC)
          -- all says clauseEval = -1
          simpa using this
        simp [hclause1] at this
      · rfl
    simp [hDNF, hψ]
  · have hDNF1 : (DNFFormula.mk ψ.clauses).eval x = 1 := by
      rcases Int.units_eq_one_or ((DNFFormula.mk ψ.clauses).eval x) with h1 | hneg
      · exact h1
      · exact absurd hneg hDNF
    have hnone : ∀ C ∈ ψ.clauses, C.eval x ≠ -1 := by
      intro C hC hCx
      exact hDNF ((DNFFormula.eval_eq_neg_one_iff _ x).2 ⟨C, hC, hCx⟩)
    have hψ : ψ.eval (fun i ↦ -x i) = -1 := by
      simp only [CNFFormula.eval]
      split_ifs with hall
      · rfl
      · -- not all clauses true at -x; some clause is false at -x, i.e. term true at x
        have hnotall : ¬ ψ.clauses.all (fun C ↦ clauseEval C (fun i ↦ -x i) = -1) := hall
        obtain ⟨C, hC, hCfail⟩ : ∃ C ∈ ψ.clauses, clauseEval C (fun i ↦ -x i) ≠ -1 := by
          simpa [List.all_eq_true, decide_eq_true_eq] using hnotall
        have hC1 : clauseEval C (fun i ↦ -x i) = 1 := by
          rcases Int.units_eq_one_or (clauseEval C (fun i ↦ -x i)) with h1 | hneg
          · exact h1
          · exact absurd hneg hCfail
        exact absurd ((clauseEval_neg_iff_termEval C x).1 hC1) (hnone C hC)
    simp [hDNF1, hψ]

end CNFFormula

/-! ## Complexity predicates (Definition 4.3) -/

def HasDNFSizeLE (f : BooleanFunction n) (s : ℕ) : Prop :=
  ∃ φ : DNFFormula n, φ.size ≤ s ∧ φ.toBooleanFunction = f

def HasDNFWidthLE (f : BooleanFunction n) (w : ℕ) : Prop :=
  ∃ φ : DNFFormula n, φ.width ≤ w ∧ φ.toBooleanFunction = f

def HasCNFSizeLE (f : BooleanFunction n) (s : ℕ) : Prop :=
  ∃ ψ : CNFFormula n, ψ.size ≤ s ∧ ψ.toBooleanFunction = f

def HasCNFWidthLE (f : BooleanFunction n) (w : ℕ) : Prop :=
  ∃ ψ : CNFFormula n, ψ.width ≤ w ∧ ψ.toBooleanFunction = f

/-- Exercise 4.2 consequence: dual of a size/width-bounded CNF is a size/width-bounded DNF. -/
theorem hasDNFSizeWidth_of_hasCNFSizeWidth
    {f : BooleanFunction n} {s w : ℕ}
    (hs : HasCNFSizeLE f s) (hw : HasCNFWidthLE f w) :
    HasDNFSizeLE (CNFFormula.booleanDual f) s ∧
      HasDNFWidthLE (CNFFormula.booleanDual f) w := by
  obtain ⟨ψ, hsize, rfl⟩ := hs
  obtain ⟨ψ', hwidth, hψ'⟩ := hw
  refine ⟨
    ⟨CNFFormula.switchAndOr ψ,
      by simpa [CNFFormula.switchAndOr, DNFFormula.size, CNFFormula.size] using hsize,
      by rw [CNFFormula.switchAndOr_toBooleanFunction]⟩,
    ?_⟩
  have hφ :
      (CNFFormula.switchAndOr ψ').toBooleanFunction =
        CNFFormula.booleanDual ψ.toBooleanFunction := by
    rw [CNFFormula.switchAndOr_toBooleanFunction, hψ']
  refine ⟨CNFFormula.switchAndOr ψ', ?_, hφ⟩
  change (DNFFormula.mk ψ'.clauses).width ≤ w
  simpa [CNFFormula.width] using hwidth

/-! ## Exercise 4.1: minterm expansion -/

/-- Canonical minterm DNF for a Boolean function. -/
noncomputable def mintermDNF (f : BooleanFunction n) : DNFFormula n := by
  classical
  exact
    ⟨(Finset.univ.filter fun x : {−1,1}^[n] ↦ f x = -1).toList.map DNFTerm.minterm⟩

theorem size_mintermDNF_le (f : BooleanFunction n) :
    (mintermDNF f).size ≤ 2 ^ n := by
  classical
  simp only [mintermDNF, DNFFormula.size, List.length_map, Finset.length_toList]
  exact (Finset.card_le_univ _).trans_eq
    (by simp [Fintype.card_pi, Sign])

theorem width_mintermDNF_le (f : BooleanFunction n) :
    (mintermDNF f).width ≤ n := by
  classical
  rw [DNFFormula.width_le_iff]
  intro T hT
  simp only [mintermDNF, List.mem_map, Finset.mem_toList] at hT
  rcases hT with ⟨x, _, rfl⟩
  exact (DNFTerm.width_minterm x).le

theorem mintermDNF_toBooleanFunction (f : BooleanFunction n) :
    (mintermDNF f).toBooleanFunction = f := by
  classical
  funext x
  change (mintermDNF f).eval x = f x
  rcases Int.units_eq_one_or (f x) with hf | hf
  · -- f x = 1
    have hnone : ∀ T ∈ (mintermDNF f).terms, T.eval x ≠ -1 := by
      intro T hT hTx
      simp only [mintermDNF, List.mem_map, Finset.mem_toList, Finset.mem_filter,
        Finset.mem_univ, true_and] at hT
      rcases hT with ⟨y, hy, rfl⟩
      have : y = x := (DNFTerm.eval_minterm_eq_neg_one_iff y x).1 hTx |>.symm
      simp [this, hf] at hy
    have hany : ((mintermDNF f).terms.any fun T ↦ T.eval x = -1) = false := by
      simp only [List.any_eq_false, decide_eq_true_eq]
      exact hnone
    simp [DNFFormula.eval, hany, hf]
  · -- f x = -1
    have hmem : DNFTerm.minterm x ∈ (mintermDNF f).terms := by
      simp only [mintermDNF, List.mem_map, Finset.mem_toList, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨x, hf, rfl⟩
    have hTx : (DNFTerm.minterm x).eval x = -1 :=
      (DNFTerm.eval_minterm_eq_neg_one_iff x x).2 rfl
    have hany : ((mintermDNF f).terms.any fun T ↦ T.eval x = -1) = true := by
      simp only [List.any_eq_true, decide_eq_true_eq]
      exact ⟨_, hmem, hTx⟩
    simp [DNFFormula.eval, hany, hf]

/-- Exercise 4.1. -/
theorem exists_DNFFormula_size_width_bound (f : BooleanFunction n) :
    ∃ φ : DNFFormula n, φ.size ≤ 2 ^ n ∧ φ.width ≤ n ∧ φ.toBooleanFunction = f :=
  ⟨mintermDNF f, size_mintermDNF_le f, width_mintermDNF_le f, mintermDNF_toBooleanFunction f⟩

theorem hasDNFSizeLE_two_pow (f : BooleanFunction n) : HasDNFSizeLE f (2 ^ n) := by
  obtain ⟨φ, hs, _, hφ⟩ := exists_DNFFormula_size_width_bound f
  exact ⟨φ, hs, hφ⟩

theorem hasDNFWidthLE_dimension (f : BooleanFunction n) : HasDNFWidthLE f n := by
  obtain ⟨φ, _, hw, hφ⟩ := exists_DNFFormula_size_width_bound f
  exact ⟨φ, hw, hφ⟩

/-- O'Donnell, Definition 4.3: least DNF size. -/
noncomputable def DNFsize (f : BooleanFunction n) : ℕ :=
  sInf {s : ℕ | HasDNFSizeLE f s}

/-- O'Donnell, Definition 4.3: least DNF width. -/
noncomputable def DNFwidth (f : BooleanFunction n) : ℕ :=
  sInf {w : ℕ | HasDNFWidthLE f w}

theorem hasDNFSizeLE_DNFsize (f : BooleanFunction n) : HasDNFSizeLE f (DNFsize f) := by
  classical
  have hne : {s : ℕ | HasDNFSizeLE f s}.Nonempty := ⟨2 ^ n, hasDNFSizeLE_two_pow f⟩
  exact Nat.sInf_mem hne

theorem hasDNFWidthLE_DNFwidth (f : BooleanFunction n) : HasDNFWidthLE f (DNFwidth f) := by
  classical
  have hne : {w : ℕ | HasDNFWidthLE f w}.Nonempty := ⟨n, hasDNFWidthLE_dimension f⟩
  exact Nat.sInf_mem hne

/-! ## Example 4.2: Sort₃ -/

def signToBit (s : Sign) : Bool := decide (s = (-1 : Sign))

/-- O'Donnell's `Sort₃` via the canonical bit-to-sign embedding `1 ↦ -1`. -/
def sort3 : BooleanFunction 3 := fun x ↦
  let b0 := signToBit (x 0)
  let b1 := signToBit (x 1)
  let b2 := signToBit (x 2)
  if (b0 ≤ b1 ∧ b1 ≤ b2) ∨ (b2 ≤ b1 ∧ b1 ≤ b0) then -1 else 1

/-- The three-term reduction of the displayed DNF in Example 4.2. -/
def sort3ReducedDNF : DNFFormula 3 where
  terms :=
    [ DNFTerm.pair 0 1 (-1) (-1) (by decide)
    , DNFTerm.pair 1 2 1 1 (by decide)
    , DNFTerm.pair 0 2 1 (-1) (by decide) ]

/-- Example 4.2's displayed four-term DNF; its last term is redundant. -/
def sort3DNF : DNFFormula 3 where
  terms := sort3ReducedDNF.terms ++ [DNFTerm.pair 0 2 (-1) 1 (by decide)]

theorem sort3ReducedDNF_toBooleanFunction : sort3ReducedDNF.toBooleanFunction = sort3 := by
  decide

theorem sort3DNF_toBooleanFunction : sort3DNF.toBooleanFunction = sort3 := by
  decide

theorem size_sort3ReducedDNF : sort3ReducedDNF.size = 3 := rfl

theorem width_sort3ReducedDNF : sort3ReducedDNF.width = 2 := by
  simp [sort3ReducedDNF, DNFFormula.width]

theorem size_sort3DNF : sort3DNF.size = 4 := rfl

theorem width_sort3DNF : sort3DNF.width = 2 := by
  simp [sort3DNF, sort3ReducedDNF, DNFFormula.width]

/-! ## Proposition 4.7: total influence of width-`w` DNFs -/

/-- `(-1)`-pivotal coordinates (book Exercise 2.10 form). -/
def IsNegOnePivotal (f : BooleanFunction n) (i : Fin n) (x : {−1,1}^[n]) : Prop :=
  f x = -1 ∧ IsPivotal f i x

noncomputable instance decidableIsNegOnePivotal (f : BooleanFunction n) (i : Fin n)
    (x : {−1,1}^[n]) : Decidable (IsNegOnePivotal f i x) := by
  classical infer_instance

/-- A satisfied DNF term contains every `(-1)`-pivotal coordinate. -/
theorem card_negOnePivotal_le_term_width (φ : DNFFormula n) (x : {−1,1}^[n])
    (T : DNFTerm n) (hT : T ∈ φ.terms) (hTx : T.eval x = -1) :
    (Finset.univ.filter fun i ↦ IsNegOnePivotal φ.toBooleanFunction i x).card ≤
      T.width := by
  classical
  have hφx : φ.eval x = -1 := (DNFFormula.eval_eq_neg_one_iff φ x).2 ⟨T, hT, hTx⟩
  let idx := (T.literals.map Literal.index).toFinset
  have hsub :
      (Finset.univ.filter fun i ↦ IsNegOnePivotal φ.toBooleanFunction i x) ⊆ idx := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsNegOnePivotal,
      DNFFormula.toBooleanFunction] at hi
    rcases hi with ⟨_, hpiv⟩
    by_contra hnot
    simp only [idx, List.mem_toFinset, List.mem_map, not_exists, not_and] at hnot
    have hTflip : T.eval (flipCoordinate x i) = -1 := by
      rw [DNFTerm.eval_eq_neg_one_iff]
      intro ℓ hℓ
      have hne : ℓ.index ≠ i := fun heq ↦ hnot ℓ hℓ heq
      rw [show flipCoordinate x i ℓ.index = x ℓ.index by
        simp [flipCoordinate, setCoordinate, Function.update_of_ne hne]]
      exact (DNFTerm.eval_eq_neg_one_iff T x).1 hTx ℓ hℓ
    have hφflip : φ.eval (flipCoordinate x i) = -1 :=
      (DNFFormula.eval_eq_neg_one_iff φ _).2 ⟨T, hT, hTflip⟩
    exact hpiv (hφx.trans hφflip.symm)
  have hcard_idx : idx.card ≤ T.width := by
    simpa [idx, DNFTerm.width] using
      (List.toFinset_card_le (T.literals.map Literal.index))
  exact (Finset.card_le_card hsub).trans hcard_idx

/-- On any input, a width-`w` DNF has at most `w` many `(-1)`-pivotal coordinates. -/
theorem card_negOnePivotal_le_width (φ : DNFFormula n) (x : {−1,1}^[n]) :
    (Finset.univ.filter fun i ↦ IsNegOnePivotal φ.toBooleanFunction i x).card ≤
      φ.width := by
  classical
  by_cases hfx : φ.eval x = -1
  · obtain ⟨T, hT, hTx⟩ := (DNFFormula.eval_eq_neg_one_iff φ x).1 hfx
    exact (card_negOnePivotal_le_term_width φ x T hT hTx).trans
      (DNFFormula.width_le_of_mem φ hT)
  · have hempty :
        (Finset.univ.filter fun i ↦ IsNegOnePivotal φ.toBooleanFunction i x) = ∅ := by
      ext i
      simp [IsNegOnePivotal, DNFFormula.toBooleanFunction, hfx]
    simp [hempty]

/-- For a fixed coordinate, `Inf_i[f] = 2 Pr[(-1)-pivotal]`. -/
theorem booleanInfluence_eq_two_mul_negOnePivotal_probability
    (f : BooleanFunction n) (i : Fin n) :
    booleanInfluence f i =
      2 * uniformProbability (IsNegOnePivotal f i) := by
  classical
  have hflip_piv (x : {−1,1}^[n]) :
      IsPivotal f i x ↔ IsPivotal f i (flipCoordinate x i) := by
    simp [IsPivotal, flipCoordinate_flipCoordinate, ne_comm]
  let Sneg := Finset.univ.filter fun x ↦ IsNegOnePivotal f i x
  let Spos := Finset.univ.filter fun x ↦ IsPivotal f i x ∧ f x = 1
  let Spiv := Finset.univ.filter fun x ↦ IsPivotal f i x
  have hsplit : Spiv = Sneg ∪ Spos := by
    ext x
    simp only [Spiv, Sneg, Spos, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, IsNegOnePivotal]
    constructor
    · intro hp
      rcases Int.units_eq_one_or (f x) with hx | hx
      · exact Or.inr ⟨hp, hx⟩
      · exact Or.inl ⟨hx, hp⟩
    · rintro (⟨_, hp⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint Sneg Spos := by
    rw [Finset.disjoint_left]
    intro x hxN hxP
    simp only [Sneg, Spos, Finset.mem_filter, IsNegOnePivotal] at hxN hxP
    exact absurd hxP.2.2 (by simp [hxN.2.1])
  have hbij : Sneg.card = Spos.card := by
    refine Finset.card_bij (fun x _ ↦ flipCoordinate x i)
      (fun x hx ↦ by
        simp only [Sneg, Spos, Finset.mem_filter, Finset.mem_univ, true_and,
          IsNegOnePivotal] at hx ⊢
        rcases hx with ⟨hneg, hp⟩
        refine ⟨(hflip_piv x).1 hp, ?_⟩
        rcases Int.units_eq_one_or (f (flipCoordinate x i)) with hf | hf
        · exact hf
        · exact absurd (hneg.trans hf.symm) hp)
      (fun x y _ _ hxy ↦ by
        simpa using congrArg (fun z ↦ flipCoordinate z i) hxy)
      (fun y hy ↦ by
        simp only [Spos, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        rcases hy with ⟨hp, hone⟩
        refine ⟨flipCoordinate y i, ?_, by simp⟩
        simp only [Sneg, Finset.mem_filter, Finset.mem_univ, true_and, IsNegOnePivotal]
        refine ⟨?_, (hflip_piv y).1 hp⟩
        rcases Int.units_eq_one_or (f (flipCoordinate y i)) with hf | hf
        · exact absurd (hone.trans hf.symm) hp
        · exact hf)
  have hcard_piv : Spiv.card = 2 * Sneg.card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj, hbij, two_mul]
  -- booleanInfluence = |Spiv| / 2^n and Pr[negOne] = |Sneg| / 2^n
  have hInf : booleanInfluence f i = (Spiv.card : ℝ) / Fintype.card ({−1,1}^[n]) := by
    classical
    change uniformProbability (IsPivotal f i) =
      (Spiv.card : ℝ) / Fintype.card ({−1,1}^[n])
    rw [uniformProbability, Fintype.expect_eq_sum_div_card]
    simp [Spiv, Finset.sum_boole]
  have hPr : uniformProbability (IsNegOnePivotal f i) =
      (Sneg.card : ℝ) / Fintype.card ({−1,1}^[n]) := by
    rw [uniformProbability, Fintype.expect_eq_sum_div_card]
    simp [Sneg, Finset.sum_boole]
  rw [hInf, hPr, hcard_piv]
  field_simp
  norm_cast

/-- Total influence is twice the expected number of `(-1)`-pivotal coordinates. -/
theorem totalInfluence_eq_two_mul_expect_card_negOnePivotal (f : BooleanFunction n) :
    totalInfluence f.toReal =
      2 * 𝔼 x, ((Finset.univ.filter fun i ↦ IsNegOnePivotal f i x).card : ℝ) := by
  classical
  rw [totalInfluence]
  simp_rw [← booleanInfluence_eq_influence_toReal,
    booleanInfluence_eq_two_mul_negOnePivotal_probability]
  calc
    (∑ i, 2 * uniformProbability (IsNegOnePivotal f i)) =
        2 * ∑ i, uniformProbability (IsNegOnePivotal f i) := by
      simp [Finset.mul_sum]
    _ = 2 * ∑ i, 𝔼 x, (if IsNegOnePivotal f i x then (1 : ℝ) else 0) := by
      simp only [uniformProbability]
    _ = 2 * 𝔼 x, ∑ i, (if IsNegOnePivotal f i x then (1 : ℝ) else 0) := by
      rw [Finset.expect_sum_comm]
    _ = 2 * 𝔼 x, ((Finset.univ.filter fun i ↦ IsNegOnePivotal f i x).card : ℝ) := by
      congr 1
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- O'Donnell, Proposition 4.7. -/
theorem totalInfluence_le_two_mul_of_hasDNFWidthLE
    {f : BooleanFunction n} {w : ℕ} (hf : HasDNFWidthLE f w) :
    totalInfluence f.toReal ≤ 2 * w := by
  classical
  obtain ⟨φ, hwidth, rfl⟩ := hf
  rw [totalInfluence_eq_two_mul_expect_card_negOnePivotal]
  have hpoint (x : {−1,1}^[n]) :
      ((Finset.univ.filter fun i ↦ IsNegOnePivotal φ.toBooleanFunction i x).card : ℝ) ≤
        (w : ℝ) := by
    exact_mod_cast (card_negOnePivotal_le_width φ x).trans hwidth
  have hexpect :
      (𝔼 x, ((Finset.univ.filter fun i ↦
          IsNegOnePivotal φ.toBooleanFunction i x).card : ℝ)) ≤ (w : ℝ) :=
    Finset.expect_le Finset.univ_nonempty fun x _ ↦ hpoint x
  nlinarith

/-- O'Donnell, Corollary 4.8. -/
theorem isFourierSpectrumConcentratedUpTo_of_hasDNFWidthLE
    {f : BooleanFunction n} {w : ℕ} (hf : HasDNFWidthLE f w)
    {ε : ℝ} (hε : 0 < ε) :
    IsFourierSpectrumConcentratedUpTo f.toReal ε (2 * w / ε) := by
  have hI := totalInfluence_le_two_mul_of_hasDNFWidthLE hf
  have hbase := isFourierSpectrumConcentratedUpTo_totalInfluence_div f.toReal hε
  exact hbase.mono_cutoff (div_le_div_of_nonneg_right hI hε.le)

/-! ## Proposition 4.9: width truncation of size-`s` DNFs -/

/-- Two literals of a term with the same index are equal (indices are nodup). -/
theorem DNFTerm.eq_of_mem_of_index_eq (T : DNFTerm n) {ℓ₁ ℓ₂ : Literal n}
    (h1 : ℓ₁ ∈ T.literals) (h2 : ℓ₂ ∈ T.literals) (hi : ℓ₁.index = ℓ₂.index) :
    ℓ₁ = ℓ₂ :=
  List.inj_on_of_nodup_map T.nodupIndices h1 h2 hi

/-- The unique literal of a term with a given support index. -/
noncomputable def DNFTerm.literalAt (T : DNFTerm n) (i : Fin n) (hi : i ∈ T.support) :
    Literal n := by
  classical
  have h : ∃ ℓ ∈ T.literals, ℓ.index = i := by
    simpa [DNFTerm.support, List.mem_toFinset, List.mem_map] using hi
  exact Classical.choose h

theorem DNFTerm.literalAt_mem (T : DNFTerm n) (i : Fin n) (hi : i ∈ T.support) :
    T.literalAt i hi ∈ T.literals := by
  classical
  have h : ∃ ℓ ∈ T.literals, ℓ.index = i := by
    simpa [DNFTerm.support, List.mem_toFinset, List.mem_map] using hi
  exact (Classical.choose_spec h).1

theorem DNFTerm.literalAt_index (T : DNFTerm n) (i : Fin n) (hi : i ∈ T.support) :
    (T.literalAt i hi).index = i := by
  classical
  have h : ∃ ℓ ∈ T.literals, ℓ.index = i := by
    simpa [DNFTerm.support, List.mem_toFinset, List.mem_map] using hi
  exact (Classical.choose_spec h).2

theorem DNFTerm.mem_support_of_mem_literals (T : DNFTerm n) {ℓ : Literal n}
    (hℓ : ℓ ∈ T.literals) : ℓ.index ∈ T.support := by
  simpa [DNFTerm.support, List.mem_toFinset] using List.mem_map_of_mem hℓ

theorem DNFTerm.literalAt_eq (T : DNFTerm n) {ℓ : Literal n} (hℓ : ℓ ∈ T.literals) :
    T.literalAt ℓ.index (T.mem_support_of_mem_literals hℓ) = ℓ :=
  T.eq_of_mem_of_index_eq (T.literalAt_mem _ _) hℓ (T.literalAt_index _ _)

/-- Required sign on a support coordinate. -/
noncomputable def DNFTerm.requiredAt (T : DNFTerm n) (i : Fin n) (hi : i ∈ T.support) : Sign :=
  (T.literalAt i hi).required

theorem DNFTerm.eval_eq_neg_one_iff_requiredAt (T : DNFTerm n) (x : {−1,1}^[n]) :
    T.eval x = -1 ↔ ∀ i : Fin n, ∀ hi : i ∈ T.support, x i = T.requiredAt i hi := by
  classical
  constructor
  · intro hx i hi
    have := (DNFTerm.eval_eq_neg_one_iff T x).1 hx (T.literalAt i hi) (T.literalAt_mem i hi)
    simpa [DNFTerm.requiredAt, T.literalAt_index i hi] using this
  · intro h
    rw [DNFTerm.eval_eq_neg_one_iff]
    intro ℓ hℓ
    have hi : ℓ.index ∈ T.support := T.mem_support_of_mem_literals hℓ
    have hreq := h ℓ.index hi
    have hℓ' : T.literalAt ℓ.index hi = ℓ := T.literalAt_eq hℓ
    simpa [hℓ', DNFTerm.requiredAt] using hreq

/-- Complements of a term support. -/
abbrev DNFTerm.Outside (T : DNFTerm n) := {i : Fin n // i ∉ T.support}

/-- Satisfying assignments of a term are free on the complement of its support. -/
noncomputable def DNFTerm.satisfyingEquiv (T : DNFTerm n) :
    {x : {−1,1}^[n] // T.eval x = -1} ≃ (T.Outside → Sign) where
  toFun p i := p.1 i.1
  invFun z := by
    classical
    refine ⟨fun i ↦ if hi : i ∈ T.support then T.requiredAt i hi else z ⟨i, hi⟩, ?_⟩
    rw [T.eval_eq_neg_one_iff_requiredAt]
    intro i hi
    simp [hi]
  left_inv := by
    classical
    intro ⟨x, hx⟩
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ T.support
    · have hx' := (T.eval_eq_neg_one_iff_requiredAt x).1 hx i hi
      simp [hi, hx']
    · simp [hi]
  right_inv := by
    classical
    intro z
    funext i
    simp [i.2]

theorem DNFTerm.card_eval_neg_one (T : DNFTerm n) :
    (Finset.univ.filter fun x : {−1,1}^[n] ↦ T.eval x = -1).card =
      2 ^ (n - T.width) := by
  classical
  have hcard := Fintype.card_congr T.satisfyingEquiv
  change Fintype.card {x : {−1,1}^[n] // T.eval x = -1} =
      Fintype.card (T.Outside → Sign) at hcard
  have hleft : Fintype.card {x : {−1,1}^[n] // T.eval x = -1} =
      (Finset.univ.filter fun x : {−1,1}^[n] ↦ T.eval x = -1).card := by
    simp [Fintype.card_subtype]
  have hright : Fintype.card (T.Outside → Sign) = 2 ^ (n - T.support.card) := by
    have hcompl : Fintype.card T.Outside = n - T.support.card := by
      classical
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    rw [Fintype.card_fun, Fintype.card_units_int, hcompl]
  rw [hleft.symm, hcard, hright, T.card_support]

/-- Exact True-probability of a DNF term. -/
theorem uniformProbability_DNFTerm_eval_neg_one (T : DNFTerm n) :
    uniformProbability (fun x ↦ T.eval x = -1) = ((2 : ℝ) ^ T.width)⁻¹ := by
  classical
  rw [uniformProbability, Fintype.expect_eq_sum_div_card]
  simp only [Finset.sum_boole]
  have hden : (Fintype.card ({−1,1}^[n]) : ℝ) = (2 : ℝ) ^ n := by
    simp [Fintype.card_pi, Sign]
  rw [T.card_eval_neg_one, hden]
  have hw : T.width ≤ n := T.width_le_dimension
  have hpow : ((2 ^ (n - T.width) : ℕ) : ℝ) = (2 : ℝ) ^ (n - T.width) := by norm_cast
  rw [hpow]
  have hsub : (2 : ℝ) ^ (n - T.width) = (2 : ℝ) ^ n * ((2 : ℝ) ^ T.width)⁻¹ :=
    pow_sub₀ (2 : ℝ) (by norm_num) hw
  rw [hsub, mul_div_cancel_left₀ _ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))]

/-- Expectation of a list-sum factors termwise. -/
theorem expect_sum_list_map {Ω : Type*} [Fintype Ω] [Nonempty Ω] {α : Type*}
    (l : List α) (f : α → Ω → ℝ) :
    (𝔼 x, (l.map fun a ↦ f a x).sum) = (l.map fun a ↦ 𝔼 x, f a x).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.expect_add_distrib, ih]

/-- Book cutoff `⌈log₂(s / ε)⌉` for DNF width truncation. -/
noncomputable def dnfWidthTruncationCutoff (s : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.logb 2 ((s : ℝ) / ε)⌉₊

theorem mul_inv_two_pow_dnfWidthTruncationCutoff_le
    (s : ℕ) {ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    (s : ℝ) * ((2 : ℝ) ^ dnfWidthTruncationCutoff s ε)⁻¹ ≤ ε := by
  let ratio : ℝ := (s : ℝ) / ε
  have hratio : 0 < ratio := div_pos (by exact_mod_cast hs) hε
  have hlog : Real.logb 2 ratio ≤ (dnfWidthTruncationCutoff s ε : ℝ) := Nat.le_ceil _
  have hratioPow : ratio ≤ (2 : ℝ) ^ dnfWidthTruncationCutoff s ε := by
    have hrpow := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hratio).1 hlog
    simpa [Real.rpow_natCast] using hrpow
  have hsPow : (s : ℝ) ≤ ε * (2 : ℝ) ^ dnfWidthTruncationCutoff s ε := by
    have := (div_le_iff₀ hε).1 hratioPow
    simpa [ratio, mul_comm] using this
  rw [← div_eq_mul_inv]
  exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ dnfWidthTruncationCutoff s ε)).2 hsPow

theorem DNFFormula.eval_truncateWidth_eq_neg_one_of
    (φ : DNFFormula n) (w : ℕ) {x : {−1,1}^[n]}
    (hx : (φ.truncateWidth w).eval x = -1) :
    φ.eval x = -1 := by
  obtain ⟨T, hT, hTx⟩ := (DNFFormula.eval_eq_neg_one_iff _ x).1 hx
  exact (DNFFormula.eval_eq_neg_one_iff φ x).2 ⟨T, (List.mem_filter.mp hT).1, hTx⟩

/-- Disagreement after truncation is witnessed by a deleted True term. -/
theorem exists_deleted_term_of_eval_ne_truncateWidth
    (φ : DNFFormula n) (w : ℕ) {x : {−1,1}^[n]}
    (hne : φ.eval x ≠ (φ.truncateWidth w).eval x) :
    ∃ T ∈ φ.terms, w < T.width ∧ T.eval x = -1 := by
  classical
  have hφ : φ.eval x = -1 := by
    rcases Int.units_eq_one_or (φ.eval x) with h1 | hneg
    · rcases Int.units_eq_one_or ((φ.truncateWidth w).eval x) with ht1 | htneg
      · exact False.elim (hne (h1.trans ht1.symm))
      · have hφ' := DNFFormula.eval_truncateWidth_eq_neg_one_of φ w htneg
        -- hφ' : φ.eval x = -1, h1 : φ.eval x = 1
        exact False.elim <| (by decide : (1 : Sign) ≠ -1) (h1.symm.trans hφ')
    · exact hneg
  have htr : (φ.truncateWidth w).eval x = 1 := by
    rcases Int.units_eq_one_or ((φ.truncateWidth w).eval x) with ht | ht
    · exact ht
    · exact False.elim (hne (hφ.trans ht.symm))
  obtain ⟨T, hT, hTx⟩ := (DNFFormula.eval_eq_neg_one_iff φ x).1 hφ
  refine ⟨T, hT, ?_, hTx⟩
  by_contra hle
  have hle' : T.width ≤ w := Nat.not_lt.mp hle
  have hmem : T ∈ (φ.truncateWidth w).terms := by
    simp [DNFFormula.truncateWidth, List.mem_filter, hT, hle']
  have : (φ.truncateWidth w).eval x = -1 :=
    (DNFFormula.eval_eq_neg_one_iff _ x).2 ⟨T, hmem, hTx⟩
  simp [htr] at this

/-- O'Donnell, Proposition 4.9 with an explicit size parameter `s ≥ DNFsize`. -/
theorem relativeHammingDist_truncateWidth_le_of_size_le
    (φ : DNFFormula n) {s : ℕ} (hsφ : φ.size ≤ s) {ε : ℝ} (hε : 0 < ε) :
    relativeHammingDist φ.toBooleanFunction
      (φ.truncateWidth (dnfWidthTruncationCutoff s ε)).toBooleanFunction ≤ ε := by
  classical
  let w := dnfWidthTruncationCutoff s ε
  rw [← uniformProbability_ne_eq_relativeHammingDist]
  change uniformProbability
      (fun x ↦ φ.eval x ≠ (φ.truncateWidth w).eval x) ≤ ε
  by_cases hs : s = 0
  · have hφ0 : φ.size = 0 := by omega
    have hterms : φ.terms = [] := List.eq_nil_of_length_eq_zero hφ0
    have hprob :
        uniformProbability (fun x ↦ φ.eval x ≠ (φ.truncateWidth w).eval x) = 0 := by
      simp [uniformProbability, DNFFormula.truncateWidth, hterms, DNFFormula.eval]
    rw [hprob]
    exact hε.le
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    let deleted := φ.terms.filter fun T ↦ decide (w < T.width)
    have hpoint (x : {−1,1}^[n]) :
        (if φ.eval x ≠ (φ.truncateWidth w).eval x then (1 : ℝ) else 0) ≤
          (deleted.map fun T ↦ if T.eval x = -1 then (1 : ℝ) else 0).sum := by
      by_cases hne : φ.eval x ≠ (φ.truncateWidth w).eval x
      · rw [if_pos hne]
        obtain ⟨T, hT, hwT, hTx⟩ := exists_deleted_term_of_eval_ne_truncateWidth φ w hne
        have hmem : T ∈ deleted := by
          simp [deleted, List.mem_filter, hT, hwT]
        have hnonneg : ∀ y ∈ deleted.map fun U ↦ if U.eval x = -1 then (1 : ℝ) else 0,
            0 ≤ y := by
          intro y hy
          obtain ⟨U, _, rfl⟩ := List.mem_map.mp hy
          split_ifs <;> norm_num
        have hmem' : (if T.eval x = -1 then (1 : ℝ) else 0) ∈
            deleted.map fun U ↦ if U.eval x = -1 then (1 : ℝ) else 0 :=
          List.mem_map_of_mem hmem
        simpa [hTx] using List.single_le_sum hnonneg _ hmem'
      · have : (if φ.eval x ≠ (φ.truncateWidth w).eval x then (1 : ℝ) else 0) = 0 := by
          simp [hne]
        rw [this]
        exact List.sum_nonneg fun y hy ↦ by
          obtain ⟨U, _, rfl⟩ := List.mem_map.mp hy
          split_ifs <;> norm_num
    have hexpect_le :
        (𝔼 x, if φ.eval x ≠ (φ.truncateWidth w).eval x then (1 : ℝ) else 0) ≤
          𝔼 x, (deleted.map fun T ↦ if T.eval x = -1 then (1 : ℝ) else 0).sum :=
      Finset.expect_le_expect fun x _ ↦ hpoint x
    have hswap :=
      expect_sum_list_map deleted (fun T x ↦ if T.eval x = -1 then (1 : ℝ) else 0)
    have hterms :
        (deleted.map fun T ↦ 𝔼 x, if T.eval x = -1 then (1 : ℝ) else 0).sum =
          (deleted.map fun T ↦ ((2 : ℝ) ^ T.width)⁻¹).sum := by
      refine congrArg List.sum ?_
      refine List.map_congr_left ?_
      intro T _
      simpa [uniformProbability] using uniformProbability_DNFTerm_eval_neg_one T
    have hwidth_bound :
        (deleted.map fun T ↦ ((2 : ℝ) ^ T.width)⁻¹).sum ≤
          deleted.length * ((2 : ℝ) ^ w)⁻¹ := by
      have hpoint' (T : DNFTerm n) (hT : T ∈ deleted) :
          ((2 : ℝ) ^ T.width)⁻¹ ≤ ((2 : ℝ) ^ w)⁻¹ := by
        have hwT : w < T.width := of_decide_eq_true (List.mem_filter.mp hT).2
        exact inv_anti₀ (pow_pos (by norm_num) _)
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_of_lt hwT))
      calc
        (deleted.map fun T ↦ ((2 : ℝ) ^ T.width)⁻¹).sum ≤
            (deleted.map fun _ : DNFTerm n ↦ ((2 : ℝ) ^ w)⁻¹).sum :=
          List.sum_le_sum fun T hT ↦ hpoint' T hT
        _ = deleted.length * ((2 : ℝ) ^ w)⁻¹ := by simp
    have hlen : (deleted.length : ℝ) ≤ (s : ℝ) := by
      have : deleted.length ≤ φ.size := List.length_filter_le _ _
      exact_mod_cast this.trans hsφ
    have hfinal :
        (𝔼 x, if φ.eval x ≠ (φ.truncateWidth w).eval x then (1 : ℝ) else 0) ≤
          (s : ℝ) * ((2 : ℝ) ^ w)⁻¹ := by
      calc
        (𝔼 x, if φ.eval x ≠ (φ.truncateWidth w).eval x then (1 : ℝ) else 0)
            ≤ 𝔼 x, (deleted.map fun T ↦ if T.eval x = -1 then (1 : ℝ) else 0).sum :=
          hexpect_le
        _ = (deleted.map fun T ↦ 𝔼 x, if T.eval x = -1 then (1 : ℝ) else 0).sum := hswap
        _ = (deleted.map fun T ↦ ((2 : ℝ) ^ T.width)⁻¹).sum := hterms
        _ ≤ deleted.length * ((2 : ℝ) ^ w)⁻¹ := hwidth_bound
        _ ≤ (s : ℝ) * ((2 : ℝ) ^ w)⁻¹ :=
          mul_le_mul_of_nonneg_right hlen (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
    exact hfinal.trans (by
      simpa [w] using mul_inv_two_pow_dnfWidthTruncationCutoff_le s hspos hε)

/-- O'Donnell, Proposition 4.9 (quantitative form on a formula's own size). -/
theorem relativeHammingDist_truncateWidth_le
    (φ : DNFFormula n) {ε : ℝ} (hε : 0 < ε) :
    relativeHammingDist φ.toBooleanFunction
      (φ.truncateWidth (dnfWidthTruncationCutoff φ.size ε)).toBooleanFunction ≤ ε :=
  relativeHammingDist_truncateWidth_le_of_size_le φ le_rfl hε

/-- O'Donnell, Proposition 4.9 (existential form). -/
theorem exists_DNF_width_truncation_close
    {f : BooleanFunction n} {s : ℕ} (hf : HasDNFSizeLE f s) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : BooleanFunction n,
      HasDNFWidthLE g (dnfWidthTruncationCutoff s ε) ∧ relativeHammingDist f g ≤ ε := by
  obtain ⟨φ, hsize, rfl⟩ := hf
  let w := dnfWidthTruncationCutoff s ε
  refine ⟨(φ.truncateWidth w).toBooleanFunction,
    ⟨φ.truncateWidth w, DNFFormula.width_truncateWidth_le φ w, rfl⟩,
    relativeHammingDist_truncateWidth_le_of_size_le φ hsize hε⟩

/-! ## Exercise 3.17: concentration transfer -/

/-- Fourier coefficients commute with pointwise subtraction. -/
theorem fourierCoeff_sub (f g : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x ↦ f x - g x) S = fourierCoeff f S - fourierCoeff g S := by
  unfold fourierCoeff
  rw [show (fun x ↦ (f x - g x) * monomial S x) =
      fun x ↦ f x * monomial S x - g x * monomial S x by
    funext x
    ring]
  exact Finset.expect_sub_distrib (Finset.univ : Finset {−1,1}^[n])
    (fun x ↦ f x * monomial S x) (fun x ↦ g x * monomial S x)

/-- O'Donnell, Exercise 3.17: squared-`L²` perturbations transfer spectral concentration. -/
theorem IsFourierSpectrumConcentratedOn.transfer_of_uniformLpNorm_sub_sq_le
    (f g : {−1,1}^[n] → ℝ) (𝓕 : Set (Finset (Fin n))) {ε₁ ε₂ : ℝ}
    (hf : IsFourierSpectrumConcentratedOn f ε₁ 𝓕)
    (hfg : uniformLpNorm 2 (fun x ↦ f x - g x) ^ 2 ≤ ε₂) :
    IsFourierSpectrumConcentratedOn g (2 * (ε₁ + ε₂)) 𝓕 := by
  classical
  let outside := Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ 𝓕
  let residual : {−1,1}^[n] → ℝ := fun x ↦ f x - g x
  have hf' : ∑ S ∈ outside, fourierCoeff f S ^ 2 ≤ ε₁ := by
    simpa [IsFourierSpectrumConcentratedOn, fourierWeightOutside, fourierWeight, outside]
      using hf
  have hfg' : ∑ S : Finset (Fin n), fourierCoeff residual S ^ 2 ≤ ε₂ := by
    rw [uniformLpNorm_two_sq_eq_uniformInner, parseval] at hfg
    exact hfg
  have hsubset :
      (∑ S ∈ outside, fourierCoeff residual S ^ 2) ≤
        ∑ S : Finset (Fin n), fourierCoeff residual S ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun S _ _ ↦ sq_nonneg (fourierCoeff residual S))
  have hpoint (S : Finset (Fin n)) :
      fourierCoeff g S ^ 2 ≤
        2 * fourierCoeff f S ^ 2 + 2 * fourierCoeff residual S ^ 2 := by
    have hcoeff : fourierCoeff g S = fourierCoeff f S - fourierCoeff residual S := by
      rw [show residual = fun x ↦ f x - g x by rfl, fourierCoeff_sub]
      ring
    rw [hcoeff]
    nlinarith [sq_nonneg (fourierCoeff f S + fourierCoeff residual S)]
  unfold IsFourierSpectrumConcentratedOn fourierWeightOutside fourierWeight
  change (∑ S ∈ outside, fourierCoeff g S ^ 2) ≤ 2 * (ε₁ + ε₂)
  calc
    (∑ S ∈ outside, fourierCoeff g S ^ 2) ≤
        ∑ S ∈ outside,
          (2 * fourierCoeff f S ^ 2 + 2 * fourierCoeff residual S ^ 2) := by
      exact Finset.sum_le_sum fun S _ ↦ hpoint S
    _ = 2 * (∑ S ∈ outside, fourierCoeff f S ^ 2) +
        2 * (∑ S ∈ outside, fourierCoeff residual S ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * ε₁ + 2 * ε₂ :=
      add_le_add (mul_le_mul_of_nonneg_left hf' (by norm_num))
        (mul_le_mul_of_nonneg_left (hsubset.trans hfg') (by norm_num))
    _ = 2 * (ε₁ + ε₂) := by ring

/-! ## Decision trees as DNF and CNF formulas -/


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

/-- CNF clause excluding a path assignment (used for False leaves). -/
noncomputable def toCNFClause (path : Path n Sign) : DNFTerm n where
  literals := path.toLiterals.map Literal.negate
  nodupIndices := by
    simpa [List.map_map, Function.comp_def, Literal.negate] using
      path.toLiterals_nodupIndices

theorem width_toDNFTerm (path : Path n Sign) :
    path.toDNFTerm.width = path.length := by
  classical
  simp only [toDNFTerm, DNFTerm.width, toLiterals, length, List.length_map,
    Finset.length_toList, Finset.card_attach]

theorem width_toCNFClause (path : Path n Sign) :
    path.toCNFClause.width = path.length := by
  simp only [toCNFClause, DNFTerm.width, List.length_map, toLiterals, length,
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

/-- The path-excluding clause is false exactly on the corresponding path subcube. -/
theorem clauseEval_toCNFClause_eq_one_iff (path : Path n Sign) (x : {−1,1}^[n]) :
    CNFFormula.clauseEval path.toCNFClause x = 1 ↔
      path.Matches ((binaryCubeSignEquiv n).symm x) := by
  rw [← path.eval_toDNFTerm_eq_neg_one_iff]
  have hneg :
      (∀ ℓ ∈ path.toLiterals, ¬x ℓ.index = -ℓ.required) ↔
        ∀ ℓ ∈ path.toLiterals, ¬-x ℓ.index = ℓ.required := by
    constructor
    · intro h ℓ hℓ hx
      apply h ℓ hℓ
      calc
        x ℓ.index = -(-x ℓ.index) := by simp
        _ = -ℓ.required := congrArg Neg.neg hx
    · intro h ℓ hℓ hx
      apply h ℓ hℓ
      calc
        -x ℓ.index = -(-ℓ.required) := congrArg Neg.neg hx
        _ = ℓ.required := by simp
  simpa [toCNFClause, toDNFTerm, CNFFormula.clauseEval, Literal.negate, Literal.eval,
    List.any_map, hneg] using CNFFormula.clauseEval_neg_iff_termEval path.toDNFTerm x

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
  clauses := (T.paths.filter fun path ↦ decide (path.output = (1 : Sign))).map Path.toCNFClause

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
  simpa [Path.width_toCNFClause] using hlen

theorem eval_toCNFFormula_eq_one {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) (x : {−1,1}^[n]) :
    T.toCNFFormula.eval x = 1 ↔
      ∃ path ∈ T.paths, path.output = (1 : Sign) ∧
        path.Matches ((binaryCubeSignEquiv n).symm x) := by
  classical
  constructor
  · intro hEval
    have hnotall :
        ¬T.toCNFFormula.clauses.all
          (fun clause ↦ CNFFormula.clauseEval clause x = -1) := by
      intro hall
      simp [CNFFormula.eval, hall] at hEval
    obtain ⟨clause, hclause, hne⟩ :
        ∃ clause ∈ T.toCNFFormula.clauses,
          CNFFormula.clauseEval clause x ≠ -1 := by
      simpa [List.all_eq_true, decide_eq_true_eq] using hnotall
    simp only [toCNFFormula, List.mem_map, List.mem_filter, decide_eq_true_eq] at hclause
    rcases hclause with ⟨path, ⟨hpath, hout⟩, rfl⟩
    have hclauseOne : CNFFormula.clauseEval path.toCNFClause x = 1 := by
      rcases Int.units_eq_one_or (CNFFormula.clauseEval path.toCNFClause x) with h | h
      · exact h
      · exact absurd h hne
    exact ⟨path, hpath, hout,
      (Path.clauseEval_toCNFClause_eq_one_iff path x).1 hclauseOne⟩
  · rintro ⟨path, hpath, hout, hmatch⟩
    have hclause : path.toCNFClause ∈ T.toCNFFormula.clauses := by
      simp only [toCNFFormula, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨path, ⟨hpath, hout⟩, rfl⟩
    have hclauseOne : CNFFormula.clauseEval path.toCNFClause x = 1 :=
      (Path.clauseEval_toCNFClause_eq_one_iff path x).2 hmatch
    simp only [CNFFormula.eval]
    split_ifs with hall
    · have hclauseNeg : CNFFormula.clauseEval path.toCNFClause x = -1 := by
        exact of_decide_eq_true (List.all_eq_true.mp hall _ hclause)
      simp [hclauseOne] at hclauseNeg
    · rfl

/-- Evaluation of the CNF agrees with the tree on the sign cube. -/
theorem toCNFFormula_toBooleanFunction {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) :
    T.toCNFFormula.toBooleanFunction =
      booleanFunctionOfBinary T.eval := by
  classical
  funext x
  change T.toCNFFormula.eval x = T.eval ((binaryCubeSignEquiv n).symm x)
  obtain ⟨path, hpathMatch, huniq⟩ :=
    existsUnique_path_mem_and_matches T ((binaryCubeSignEquiv n).symm x)
  obtain ⟨hpath, hmatch⟩ := hpathMatch
  have hval : T.eval ((binaryCubeSignEquiv n).symm x) = path.output :=
    eval_eq_path_output_of_mem_of_matches T path _ hpath hmatch
  rcases Int.units_eq_one_or path.output with hout | hout
  · have hCNF : T.toCNFFormula.eval x = 1 :=
      (eval_toCNFFormula_eq_one T x).2 ⟨path, hpath, hout, hmatch⟩
    simp [hCNF, hval, hout]
  · have hnone : ¬∃ p ∈ T.paths, p.output = (1 : Sign) ∧
        p.Matches ((binaryCubeSignEquiv n).symm x) := by
      rintro ⟨p, hp, hpo, hpm⟩
      have : p = path := huniq p ⟨hp, hpm⟩
      subst p
      simp [hout] at hpo
    have hCNFNe : T.toCNFFormula.eval x ≠ 1 := by
      intro h
      exact hnone ((eval_toCNFFormula_eq_one T x).1 h)
    have hCNF : T.toCNFFormula.eval x = -1 := by
      rcases Int.units_eq_one_or (T.toCNFFormula.eval x) with hOne | hNeg
      · exact absurd hOne hCNFNe
      · exact hNeg
    simp [hCNF, hval, hout]

/-- O'Donnell, Proposition 4.5 (CNF form): a decision tree of size `s` and depth `k` yields a
CNF of size at most `s` and width at most `k`. -/
theorem hasCNFSizeWidth_of_decisionTree {available : Finset (Fin n)}
    (T : F₂DecisionTree n Sign available) :
    HasCNFSizeLE (booleanFunctionOfBinary T.eval) T.leafCount ∧
      HasCNFWidthLE (booleanFunctionOfBinary T.eval) T.depth := by
  exact ⟨
    ⟨T.toCNFFormula, T.size_toCNFFormula_le, T.toCNFFormula_toBooleanFunction⟩,
    ⟨T.toCNFFormula, T.width_toCNFFormula_le, T.toCNFFormula_toBooleanFunction⟩⟩

/-- Proposition 4.5 (CNF form) for a complete available-coordinate tree computing a sign-cube
Boolean function. -/
theorem hasCNFSizeWidth_of_computes
    (T : DecisionTree n Sign) (f : BooleanFunction n)
    (hT : T.Computes (binaryOfBooleanFunction f)) :
    HasCNFSizeLE f T.leafCount ∧ HasCNFWidthLE f T.depth := by
  have h := T.hasCNFSizeWidth_of_decisionTree
  have heq : booleanFunctionOfBinary T.eval = f := by
    funext x
    exact (congrFun hT ((binaryCubeSignEquiv n).symm x)).trans
      (by simp [binaryOfBooleanFunction])
  simpa [heq] using h

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

/-- O'Donnell, Proposition 4.5 (CNF existential form). -/
theorem exists_CNF_of_decisionTree
    (f : BooleanFunction n) (s k : ℕ)
    (T : DecisionTree n Sign)
    (hT : T.Computes (binaryOfBooleanFunction f))
    (hs : T.leafCount ≤ s) (hk : T.depth ≤ k) :
    HasCNFSizeLE f s ∧ HasCNFWidthLE f k := by
  obtain ⟨hsize, hwidth⟩ := F₂DecisionTree.hasCNFSizeWidth_of_computes T f hT
  constructor
  · obtain ⟨ψ, hψs, hψ⟩ := hsize
    exact ⟨ψ, hψs.trans hs, hψ⟩
  · obtain ⟨ψ, hψw, hψ⟩ := hwidth
    exact ⟨ψ, hψw.trans hk, hψ⟩

/-! ## Example 4.6 -/

/-- The three width-at-most-three paths shared by the printed and corrected Example 4.6 DNFs. -/
def sort3DecisionTreeDNFPrefix : List (DNFTerm 3) :=
  [ { literals := [⟨0, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩]
      nodupIndices := by decide }
  , DNFTerm.pair 0 2 1 (-1) (by decide)
  , { literals := [⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩]
      nodupIndices := by decide } ]

/-- The DNF printed in Example 4.6 of the May 2021 edition. -/
def sort3DecisionTreeDNFPrinted : DNFFormula 3 where
  terms := sort3DecisionTreeDNFPrefix ++ [DNFTerm.pair 1 2 (-1) (-1) (by decide)]

theorem size_sort3DecisionTreeDNFPrinted : sort3DecisionTreeDNFPrinted.size = 4 := rfl

theorem width_sort3DecisionTreeDNFPrinted : sort3DecisionTreeDNFPrinted.width = 3 := by
  decide

/-- The printed Example 4.6 formula disagrees with `Sort₃` on the sorted input `110`. -/
theorem sort3DecisionTreeDNFPrinted_counterexample :
    sort3DecisionTreeDNFPrinted.eval ![-1, -1, 1] = 1 ∧ sort3 ![-1, -1, 1] = -1 := by
  decide

/-- Corrected Example 4.6 formula, replacing the last printed term by `x₁ ∧ x₂`. -/
def sort3DecisionTreeDNF : DNFFormula 3 where
  terms := sort3DecisionTreeDNFPrefix ++ [DNFTerm.pair 0 1 (-1) (-1) (by decide)]

theorem size_sort3DecisionTreeDNF : sort3DecisionTreeDNF.size = 4 := rfl

theorem width_sort3DecisionTreeDNF : sort3DecisionTreeDNF.width = 3 := by
  decide

theorem sort3DecisionTreeDNF_toBooleanFunction :
    sort3DecisionTreeDNF.toBooleanFunction = sort3 := by
  decide


/-! ## Width truncation for CNF formulas -/


variable {n : ℕ}

namespace CNFFormula

@[simp] theorem booleanDual_involutive (f : BooleanFunction n) :
    booleanDual (booleanDual f) = f := by
  funext x
  simp [booleanDual]

/-- Boolean duality preserves uniform Hamming distance. -/
theorem relativeHammingDist_booleanDual (f g : BooleanFunction n) :
    relativeHammingDist (booleanDual f) (booleanDual g) =
      relativeHammingDist f g := by
  rw [← uniformProbability_ne_eq_relativeHammingDist,
    ← uniformProbability_ne_eq_relativeHammingDist]
  unfold uniformProbability
  exact Fintype.expect_equiv (signCubeNegEquiv n)
    (fun x ↦ if booleanDual f x ≠ booleanDual g x then (1 : ℝ) else 0)
    (fun x ↦ if f x ≠ g x then (1 : ℝ) else 0)
    (by intro x; simp [booleanDual, signCubeNegEquiv])

/-- Delete all CNF clauses of width greater than `w`. -/
def truncateWidth (ψ : CNFFormula n) (w : ℕ) : CNFFormula n :=
  ⟨ψ.clauses.filter fun clause ↦ decide (clause.width ≤ w)⟩

theorem width_truncateWidth_le (ψ : CNFFormula n) (w : ℕ) :
    (ψ.truncateWidth w).width ≤ w := by
  change (DNFFormula.mk (ψ.truncateWidth w).clauses).width ≤ w
  exact DNFFormula.width_truncateWidth_le (CNFFormula.switchAndOr ψ) w

theorem size_truncateWidth_le (ψ : CNFFormula n) (w : ℕ) :
    (ψ.truncateWidth w).size ≤ ψ.size :=
  List.length_filter_le _ _

@[simp] theorem switchAndOr_truncateWidth (ψ : CNFFormula n) (w : ℕ) :
    switchAndOr (ψ.truncateWidth w) = (switchAndOr ψ).truncateWidth w := rfl

/-- O'Donnell, Proposition 4.9 (CNF form), quantitatively and with the output kept in CNF. -/
theorem relativeHammingDist_truncateWidth_le_of_size_le
    (ψ : CNFFormula n) {s : ℕ} (hsψ : ψ.size ≤ s)
    {ε : ℝ} (hε : 0 < ε) :
    relativeHammingDist ψ.toBooleanFunction
      (ψ.truncateWidth (dnfWidthTruncationCutoff s ε)).toBooleanFunction ≤ ε := by
  let φ := switchAndOr ψ
  let w := dnfWidthTruncationCutoff s ε
  have hφsize : φ.size ≤ s := by
    simpa [φ, switchAndOr, DNFFormula.size, CNFFormula.size] using hsψ
  have hdnf := FABL.relativeHammingDist_truncateWidth_le_of_size_le φ hφsize hε
  calc
    relativeHammingDist ψ.toBooleanFunction (ψ.truncateWidth w).toBooleanFunction =
        relativeHammingDist (booleanDual ψ.toBooleanFunction)
          (booleanDual (ψ.truncateWidth w).toBooleanFunction) :=
      (relativeHammingDist_booleanDual _ _).symm
    _ = relativeHammingDist φ.toBooleanFunction
          (φ.truncateWidth w).toBooleanFunction := by
      rw [← switchAndOr_toBooleanFunction, ← switchAndOr_toBooleanFunction]
      rfl
    _ ≤ ε := by simpa [w] using hdnf

end CNFFormula

/-- O'Donnell, Proposition 4.9 (CNF existential form). -/
theorem exists_CNF_width_truncation_close
    {f : BooleanFunction n} {s : ℕ} (hf : HasCNFSizeLE f s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : BooleanFunction n,
      HasCNFWidthLE g (dnfWidthTruncationCutoff s ε) ∧
        relativeHammingDist f g ≤ ε := by
  obtain ⟨ψ, hsize, rfl⟩ := hf
  let w := dnfWidthTruncationCutoff s ε
  exact ⟨(ψ.truncateWidth w).toBooleanFunction,
    ⟨ψ.truncateWidth w, ψ.width_truncateWidth_le w, rfl⟩,
    ψ.relativeHammingDist_truncateWidth_le_of_size_le hsize hε⟩


/-! ## Total influence of bounded-width CNF formulas -/


variable {n : ℕ}

@[simp] theorem signValue_neg (s : Sign) : signValue (-s) = -signValue s := by
  rcases Int.units_eq_one_or s with hs | hs <;> simp [hs, signValue]

theorem sq_discreteDerivative_booleanDual (f : BooleanFunction n)
    (i : Fin n) (x : {−1,1}^[n]) :
    discreteDerivative i (CNFFormula.booleanDual f).toReal x ^ 2 =
      discreteDerivative i f.toReal (signCubeNegEquiv n x) ^ 2 := by
  simp only [discreteDerivative_apply, CNFFormula.booleanDual, BooleanFunction.toReal]
  have hplus :
      (fun j ↦ -(setCoordinate x i (1 : Sign)) j) =
        setCoordinate (signCubeNegEquiv n x) i (-1 : Sign) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [setCoordinate, signCubeNegEquiv]
    · simp [setCoordinate, signCubeNegEquiv, hji]
  have hminus :
      (fun j ↦ -(setCoordinate x i (-1 : Sign)) j) =
        setCoordinate (signCubeNegEquiv n x) i (1 : Sign) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [setCoordinate, signCubeNegEquiv]
    · simp [setCoordinate, signCubeNegEquiv, hji]
  rw [hplus, hminus]
  simp only [signValue_neg]
  ring

/-- Boolean duality preserves total influence. -/
theorem totalInfluence_booleanDual (f : BooleanFunction n) :
    totalInfluence (CNFFormula.booleanDual f).toReal = totalInfluence f.toReal := by
  unfold totalInfluence
  apply Finset.sum_congr rfl
  intro i _
  unfold influence
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  apply congrArg (fun t : ℝ ↦ t / Fintype.card ({−1,1}^[n]))
  calc
    ∑ x : {−1,1}^[n],
        discreteDerivative i (CNFFormula.booleanDual f).toReal x ^ 2 =
        ∑ x : {−1,1}^[n],
          discreteDerivative i f.toReal (signCubeNegEquiv n x) ^ 2 := by
      apply Fintype.sum_congr
      intro x
      exact sq_discreteDerivative_booleanDual f i x
    _ = ∑ x : {−1,1}^[n], discreteDerivative i f.toReal x ^ 2 := by
      simpa using (signCubeNegEquiv n).sum_comp
        (fun x ↦ discreteDerivative i f.toReal x ^ 2)

/-- O'Donnell, Proposition 4.7 (CNF form). -/
theorem totalInfluence_le_two_mul_of_hasCNFWidthLE
    {f : BooleanFunction n} {w : ℕ} (hf : HasCNFWidthLE f w) :
    totalInfluence f.toReal ≤ 2 * w := by
  obtain ⟨ψ, hψwidth, rfl⟩ := hf
  let φ := CNFFormula.switchAndOr ψ
  have hφwidth : φ.width ≤ w := by
    simpa [φ, CNFFormula.switchAndOr, CNFFormula.width] using hψwidth
  have hbound := totalInfluence_le_two_mul_of_hasDNFWidthLE
    (f := φ.toBooleanFunction) ⟨φ, hφwidth, rfl⟩
  rw [CNFFormula.switchAndOr_toBooleanFunction, totalInfluence_booleanDual] at hbound
  exact hbound


end FABL
