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

Book items: Definition 4.1, Example 4.2, Definition 4.3, Definition 4.4, Proposition 4.5,
Example 4.6, Proposition 4.7, Corollary 4.8, Proposition 4.9, Exercise 4.1, Exercise 4.2.

Formalization of Section 4.1 of O'Donnell's *Analysis of Boolean Functions*.

Representation note. The book introduces DNF syntax over `{0,1}` and then analyses
functions on `{-1,1}` with `-1 = True`. Production declarations use the sign cube: a
literal stores a required sign for a coordinate. Computed Boolean functions match the book.
-/

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

def signToBit (s : Sign) : Bool := decide (s = (1 : Sign))

/-- O'Donnell's `Sort₃` via the standard bit embedding. -/
def sort3 : BooleanFunction 3 := fun x ↦
  let b0 := signToBit (x 0)
  let b1 := signToBit (x 1)
  let b2 := signToBit (x 2)
  if (b0 ≤ b1 ∧ b1 ≤ b2) ∨ (b2 ≤ b1 ∧ b1 ≤ b0) then -1 else 1

/-- Example 4.2 DNF from the prose description (page 94). -/
def sort3DNF : DNFFormula 3 where
  terms :=
    [ DNFTerm.pair 0 1 1 1 (by decide)
    , DNFTerm.pair 1 2 (-1) (-1) (by decide)
    , DNFTerm.pair 0 2 (-1) 1 (by decide)
    , DNFTerm.pair 0 2 1 (-1) (by decide) ]

theorem size_sort3DNF : sort3DNF.size = 4 := rfl

theorem width_sort3DNF : sort3DNF.width = 2 := by
  simp [sort3DNF, DNFFormula.width]

/-! ## Proposition 4.7: total influence of width-`w` DNFs -/

/-- `(-1)`-pivotal coordinates (book Exercise 2.10 form). -/
def IsNegOnePivotal (f : BooleanFunction n) (i : Fin n) (x : {−1,1}^[n]) : Prop :=
  f x = -1 ∧ IsPivotal f i x

noncomputable instance decidableIsNegOnePivotal (f : BooleanFunction n) (i : Fin n)
    (x : {−1,1}^[n]) : Decidable (IsNegOnePivotal f i x) := by
  classical infer_instance

/-- On any input, a width-`w` DNF has at most `w` many `(-1)`-pivotal coordinates. -/
theorem card_negOnePivotal_le_width (φ : DNFFormula n) (x : {−1,1}^[n]) :
    (Finset.univ.filter fun i ↦ IsNegOnePivotal φ.toBooleanFunction i x).card ≤
      φ.width := by
  classical
  by_cases hfx : φ.eval x = -1
  · obtain ⟨T, hT, hTx⟩ := (DNFFormula.eval_eq_neg_one_iff φ x).1 hfx
    have hTw : T.width ≤ φ.width := DNFFormula.width_le_of_mem φ hT
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
        have : flipCoordinate x i ℓ.index = x ℓ.index := by
          simp [flipCoordinate, setCoordinate, Function.update_of_ne hne]
        rw [this]
        exact (DNFTerm.eval_eq_neg_one_iff T x).1 hTx ℓ hℓ
      have hφflip : φ.eval (flipCoordinate x i) = -1 :=
        (DNFFormula.eval_eq_neg_one_iff φ _).2 ⟨T, hT, hTflip⟩
      exact hpiv (hfx.trans hφflip.symm)
    have hcard_idx : idx.card ≤ T.width := by
      simpa [idx, DNFTerm.width] using
        (List.toFinset_card_le (T.literals.map Literal.index))
    exact (Finset.card_le_card hsub).trans (hcard_idx.trans hTw)
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

private theorem list_sum_const {α : Type*} (l : List α) (c : ℝ) :
    (l.map fun _ : α ↦ c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons _ l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.cast_add, Nat.cast_one]
    ring

private theorem list_sum_nonneg {l : List ℝ} (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons]
    exact add_nonneg (h a (List.mem_cons_self)) (ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx))

private theorem list_le_sum_of_mem {l : List ℝ} {x : ℝ} (hx : x ∈ l)
    (hnonneg : ∀ y ∈ l, 0 ≤ y) : x ≤ l.sum := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.sum_cons]
      exact le_add_of_nonneg_right
        (list_sum_nonneg fun y hy ↦ hnonneg y (List.mem_cons_of_mem _ hy))
    · simp only [List.sum_cons]
      exact (ih hx fun y hy ↦ hnonneg y (List.mem_cons_of_mem _ hy)).trans
        (le_add_of_nonneg_left (hnonneg a List.mem_cons_self))

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
        simpa [hTx] using list_le_sum_of_mem hmem' hnonneg
      · have : (if φ.eval x ≠ (φ.truncateWidth w).eval x then (1 : ℝ) else 0) = 0 := by
          simp [hne]
        rw [this]
        exact list_sum_nonneg fun y hy ↦ by
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
        _ = deleted.length * ((2 : ℝ) ^ w)⁻¹ := list_sum_const deleted _
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

end FABL
