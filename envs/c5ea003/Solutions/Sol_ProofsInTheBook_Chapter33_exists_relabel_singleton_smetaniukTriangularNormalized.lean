-- Prove2me | solution 1 for ProofsInTheBook.Chapter33.exists_relabel_singleton_smetaniukTriangularNormalized
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:08:42.048974+00:00
-- url     : https://prove2.me/submissions/a5ad23c3-285e-4da0-9d30-b3a4c6e6a487

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter33 -/
section
set_option autoImplicit true

open Finset
open Classical

/-!
# Chapter 33: Completing Latin squares

From "Proofs from THE BOOK":

**Latin square completion**: Any partial Latin square of order n with
at most n-1 entries can be completed to a full Latin square.

The book's proof uses Hall's marriage theorem applied row by row:
at each step, the remaining entries in each row form a system of
distinct representatives.

Point-17 status: this file now contains several genuine pieces: the
row-completion Hall step for a sparse partial square, the state update that
fills an empty row while preserving the partial Latin property and with an
exact filled-cell count, row/column/symbol relabeling infrastructure for the
normalization step in Smetaniuk's exact-cardinality induction, a reduction from
the exact case to a normalized exact case with one prescribed filled cell, the standard
extension of a Latin rectangle by one row, and the padding reduction
`completion_from_exact_cardinality_case`, which proves that the `|P| ≤ n - 1`
case reduces to the exact `|P| = n - 1` Evans case by adding legal entries one
at a time.  The complete completion theorem is also discharged for all partial
squares with at most one filled cell and for orders `0`, `1`, `2`, and `3`.
The canonical `chapter33` theorem is now stated as the full completion theorem
conditional on the exact-cardinality Evans/Smetaniuk case.  It is still not an
unconditional full Evans/Smetaniuk completion theorem.  The
remaining missing infrastructure is the exact-cardinality Smetaniuk induction:
permuting rows/columns/symbols so a singleton symbol lies on the back diagonal
and all other filled cells lie above it, applying the order-`n - 1` induction
hypothesis after deleting that diagonal cell and the last row/column, and
formalizing Smetaniuk's completion of the associated `P(L)` by column
switching.  A direct iteration of `latin_square_completion_step_from_partial`
is not valid after one whole row is added, because the current partial square
then has more than `n - 1` filled cells and the double-counting hypotheses
below no longer describe the enlarged state.

The tempting strengthened row step with fixed entries in the active row also
does not follow from the existing count alone.  After `r` completed rows and
`m = n - r` unfinished rows, Hall for a set `S` of still-empty columns can be
forced by elementary counting in the small range `|S| ≤ m - k` and in the
large range `r < |S|`, where `k` is the number of fixed entries in the active
row.  The middle range `m - k < |S| ≤ r` is exactly where the naive induction
has no contradiction from the available pair counts; this is the point where
the book uses Smetaniuk's diagonal placement and switching construction.  That
switching lemma is the honest remaining frontier for upgrading `chapter33` to
the full completion theorem.
-/

namespace ProofsInTheBook.Chapter33

/-!
### Hall's theorem as the row-by-row engine

The book completes a partial Latin square by repeatedly choosing distinct
representatives from finite availability lists.  The combinatorial engine is
Hall's marriage theorem in exactly this finite-family form.
-/





/-!
### Latin rectangles

The first Hall application in the book says that every `r × n` Latin
rectangle with `r < n` can be extended by one more row.
-/















/-!
### Proving Hall's condition from the partial Latin square structure

The premise `hHall_verified` in the Latin square completion step below can be
proved from the partial Latin square structure using double counting.

Key idea: For a set S of columns, let B be the symbols used in every column of S.
Every pair (a, j) with a ∈ B and j ∈ S corresponds to a distinct filled cell.
Since the partial Latin square has at most n-1 filled cells, |B|·|S| ≤ n-1.
If Hall's condition fails (|⋃ available(j)| < |S|), then |B| ≥ n-|S|+1, giving
|B|·|S| ≥ n, a contradiction.
-/











/-!
### Connecting to the partial Latin square representation

A partial Latin square is `P : Fin n → Fin n → Option (Fin n)` where
`P i j = some a` means cell (i,j) contains symbol a, and `P i j = none` means empty.
-/

































lemma relabelPartial_eq_some_iff {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) (i j a : Fin n) :
    relabelPartial rowPerm colPerm symPerm P i j = some a ↔
      P (rowPerm i) (colPerm j) = some (symPerm.symm a) := by
  constructor
  · intro h
    rcases (by simpa [relabelPartial] using h) with ⟨b, hb, hbmap⟩
    have hb_eq : b = symPerm.symm a := by
      rw [← hbmap]
      simp
    simpa [hb_eq] using hb
  · intro h
    simp [relabelPartial, h]







































































/-!
### Elementary complete orders

Squares with at most one filled cell, and orders `0`, `1`, `2`, and `3`, do not
need the Evans/Smetaniuk induction.
-/









































































































end ProofsInTheBook.Chapter33

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter33
-/
/- Source module: ProofsInTheBook.Chapter33Smetaniuk -/
section
set_option autoImplicit true


open Finset
open Classical

namespace ProofsInTheBook.Chapter33

/-!
# Chapter 33: Smetaniuk switching frontier

This file isolates the coordinate bookkeeping for Smetaniuk's normalized
induction.  The hard switching lemma is deliberately left as a named
proposition, not as an unproved theorem.
-/









/-!
## Improper Latin squares

Smetaniuk's induction keeps the order-`N` intermediate square as a signed
array.  A proper cell `[x]` contributes one copy of `x`; an improper cell
`[x+y-z]` contributes `+x + y - z` to every row and column balance, while a
prescribed entry is satisfied by positive syntactic occurrence.
-/



namespace SignedCell

variable {α : Type*} [DecidableEq α]



























end SignedCell





















































































































@[simp] private lemma rankLift_base {m : ℕ} (x₀ : Fin (m + 1))
    (ρ : Equiv.Perm (Fin m)) :
    rankLift x₀ ρ x₀ = 0 := by
  simp [rankLift, splitAt]

private lemma rankLift_succAbove {m : ℕ} (x₀ : Fin (m + 1))
    (ρ : Equiv.Perm (Fin m)) (i : Fin m) :
    rankLift x₀ ρ (x₀.succAbove i) = Fin.succ (ρ i) := by
  have hne : x₀.succAbove i ≠ x₀ := Fin.succAbove_ne x₀ i
  simp [rankLift, splitAt, hne]
  have hsub : (⟨x₀.succAbove i, hne⟩ : {x : Fin (m + 1) // x ≠ x₀}) =
      finSuccAboveEquivNe x₀ i := rfl
  simp [hsub]

private lemma exists_empty_column_of_card_lt {n : ℕ}
    (S : Finset (Fin n × Fin n)) (hS : S.card < n) :
    ∃ c₀ : Fin n, ∀ p ∈ S, p.2 ≠ c₀ := by
  classical
  by_contra hnone
  have hcols_all : ∀ c : Fin n, c ∈ S.image Prod.snd := by
    intro c
    by_contra hc
    exact hnone ⟨c, by
      intro p hp hpcol
      exact hc (Finset.mem_image.mpr ⟨p, hp, hpcol⟩)⟩
  have hn_le_cols : n ≤ (S.image Prod.snd).card := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (S.image Prod.snd).card := by
        exact Finset.card_le_card (by
          intro c _hc
          exact hcols_all c)
  have hcols_le_S : (S.image Prod.snd).card ≤ S.card := Finset.card_image_le
  omega



/--
Peeling normalization with one distinguished cell: fewer than `n` marked cells
can be permuted so the distinguished cell lies on the main diagonal and every
other marked cell lies strictly above it.
-/
theorem exists_perm_singleton_diagonal_strictly_above {n : ℕ}
    (S : Finset (Fin n × Fin n)) {e : Fin n × Fin n}
    (he : e ∈ S) (hS : S.card < n) :
    ∃ σ τ : Equiv.Perm (Fin n), ∃ d : Fin n,
      σ e.1 = d ∧ τ e.2 = d ∧
        ∀ p ∈ S, p ≠ e → σ p.1 < τ p.2 := by
  classical
  revert e S
  refine Nat.strong_induction_on n ?_
  intro n ih S e he hS
  cases n with
  | zero =>
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e, he⟩
      omega
  | succ m =>
      by_cases houtside : ∃ p : Fin (m + 1) × Fin (m + 1),
          p ∈ S ∧ p ≠ e ∧ p.1 ≠ e.1
      · rcases houtside with ⟨p₀, hp₀, hp₀_ne_e, hp₀_row_ne⟩
        let r₀ : Fin (m + 1) := p₀.1
        obtain ⟨c₀, hc₀⟩ := exists_empty_column_of_card_lt S hS
        have hmpos : 0 < m := by
          have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e, he⟩
          omega
        have he_row_ne : e.1 ≠ r₀ := by
          intro h
          exact hp₀_row_ne h.symm
        have he_col_ne : e.2 ≠ c₀ := hc₀ e he
        let rowIndex : Fin (m + 1) → Fin m := fun i =>
          if hi : i = r₀ then ⟨0, hmpos⟩ else (finSuccAboveEquivNe r₀).symm ⟨i, hi⟩
        let colIndex : Fin (m + 1) → Fin m := fun j =>
          if hj : j = c₀ then ⟨0, hmpos⟩ else (finSuccAboveEquivNe c₀).symm ⟨j, hj⟩
        let S' : Finset (Fin m × Fin m) :=
          (S.filter fun p => p.1 ≠ r₀).image fun p => (rowIndex p.1, colIndex p.2)
        let e' : Fin m × Fin m := (rowIndex e.1, colIndex e.2)
        have he_filter : e ∈ S.filter fun p => p.1 ≠ r₀ :=
          Finset.mem_filter.mpr ⟨he, he_row_ne⟩
        have he' : e' ∈ S' := by
          exact Finset.mem_image.mpr ⟨e, he_filter, rfl⟩
        have hfilter_subset_erase :
            (S.filter fun p => p.1 ≠ r₀) ⊆ S.erase p₀ := by
          intro p hp
          have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
          have hprow : p.1 ≠ r₀ := (Finset.mem_filter.mp hp).2
          have hpne : p ≠ p₀ := by
            intro h
            exact hprow (by simp [r₀, h])
          simp [hpS, hpne]
        have hfilter_card_le :
            (S.filter fun p => p.1 ≠ r₀).card ≤ S.card - 1 := by
          have hle := Finset.card_le_card hfilter_subset_erase
          have herase := Finset.card_erase_of_mem hp₀
          omega
        have hS'_le_filter :
            S'.card ≤ (S.filter fun p => p.1 ≠ r₀).card := by
          exact Finset.card_image_le
        have hS' : S'.card < m := by
          omega
        obtain ⟨σ', τ', d', hσ'e, hτ'e, hrec⟩ :=
          ih m (Nat.lt_succ_self m) S' he' hS'
        let σ : Equiv.Perm (Fin (m + 1)) := rankLift r₀ σ'
        let τ : Equiv.Perm (Fin (m + 1)) := rankLift c₀ τ'
        refine ⟨σ, τ, Fin.succ d', ?_, ?_, ?_⟩
        · have hrow_succ :
              r₀.succAbove (rowIndex e.1) = e.1 := by
            simp [rowIndex, he_row_ne]
            exact congrArg Subtype.val
              ((finSuccAboveEquivNe r₀).apply_symm_apply ⟨e.1, he_row_ne⟩)
          calc
            σ e.1 = σ (r₀.succAbove (rowIndex e.1)) := by rw [hrow_succ]
            _ = Fin.succ (σ' (rowIndex e.1)) :=
              rankLift_succAbove r₀ σ' (rowIndex e.1)
            _ = Fin.succ d' := by rw [hσ'e]
        · have hcol_succ :
              c₀.succAbove (colIndex e.2) = e.2 := by
            simp [colIndex, he_col_ne]
            exact congrArg Subtype.val
              ((finSuccAboveEquivNe c₀).apply_symm_apply ⟨e.2, he_col_ne⟩)
          calc
            τ e.2 = τ (c₀.succAbove (colIndex e.2)) := by rw [hcol_succ]
            _ = Fin.succ (τ' (colIndex e.2)) :=
              rankLift_succAbove c₀ τ' (colIndex e.2)
            _ = Fin.succ d' := by rw [hτ'e]
        · intro p hp hp_ne_e
          have hpcol_ne : p.2 ≠ c₀ := hc₀ p hp
          by_cases hprow : p.1 = r₀
          · have hσbase : σ p.1 = 0 := by
              rw [hprow]
              simp [σ]
            have hcol_succ :
                c₀.succAbove (colIndex p.2) = p.2 := by
              simp [colIndex, hpcol_ne]
              exact congrArg Subtype.val
                ((finSuccAboveEquivNe c₀).apply_symm_apply ⟨p.2, hpcol_ne⟩)
            have hτ :
                τ p.2 = Fin.succ (τ' (colIndex p.2)) := by
              calc
                τ p.2 = τ (c₀.succAbove (colIndex p.2)) := by rw [hcol_succ]
                _ = Fin.succ (τ' (colIndex p.2)) :=
                  rankLift_succAbove c₀ τ' (colIndex p.2)
            rw [hσbase, hτ]
            change (0 : ℕ) < (τ' (colIndex p.2)).val + 1
            omega
          · have hrow_succ :
                r₀.succAbove (rowIndex p.1) = p.1 := by
              simp [rowIndex, hprow]
              exact congrArg Subtype.val
                ((finSuccAboveEquivNe r₀).apply_symm_apply ⟨p.1, hprow⟩)
            have hcol_succ :
                c₀.succAbove (colIndex p.2) = p.2 := by
              simp [colIndex, hpcol_ne]
              exact congrArg Subtype.val
                ((finSuccAboveEquivNe c₀).apply_symm_apply ⟨p.2, hpcol_ne⟩)
            have hp_filter : p ∈ S.filter fun q => q.1 ≠ r₀ :=
              Finset.mem_filter.mpr ⟨hp, hprow⟩
            have hpS' : (rowIndex p.1, colIndex p.2) ∈ S' :=
              Finset.mem_image.mpr ⟨p, hp_filter, rfl⟩
            have hp'_ne_e' : (rowIndex p.1, colIndex p.2) ≠ e' := by
              intro hpe'
              have hrow_eq : p.1 = e.1 := by
                have hidx : rowIndex p.1 = rowIndex e.1 :=
                  congrArg Prod.fst hpe'
                have hs₁ : r₀.succAbove (rowIndex p.1) =
                    r₀.succAbove (rowIndex e.1) := by rw [hidx]
                have he_row_succ :
                    r₀.succAbove (rowIndex e.1) = e.1 := by
                  simp [rowIndex, he_row_ne]
                  exact congrArg Subtype.val
                    ((finSuccAboveEquivNe r₀).apply_symm_apply ⟨e.1, he_row_ne⟩)
                exact hrow_succ.symm.trans (hs₁.trans he_row_succ)
              have hcol_eq : p.2 = e.2 := by
                have hidx : colIndex p.2 = colIndex e.2 :=
                  congrArg Prod.snd hpe'
                have hs₁ : c₀.succAbove (colIndex p.2) =
                    c₀.succAbove (colIndex e.2) := by rw [hidx]
                have he_col_succ :
                    c₀.succAbove (colIndex e.2) = e.2 := by
                  simp [colIndex, he_col_ne]
                  exact congrArg Subtype.val
                    ((finSuccAboveEquivNe c₀).apply_symm_apply ⟨e.2, he_col_ne⟩)
                exact hcol_succ.symm.trans (hs₁.trans he_col_succ)
              exact hp_ne_e (Prod.ext hrow_eq hcol_eq)
            have hlt' : σ' (rowIndex p.1) < τ' (colIndex p.2) :=
              hrec (rowIndex p.1, colIndex p.2) hpS' hp'_ne_e'
            have hσ :
                σ p.1 = Fin.succ (σ' (rowIndex p.1)) := by
              calc
                σ p.1 = σ (r₀.succAbove (rowIndex p.1)) := by rw [hrow_succ]
                _ = Fin.succ (σ' (rowIndex p.1)) :=
                  rankLift_succAbove r₀ σ' (rowIndex p.1)
            have hτ :
                τ p.2 = Fin.succ (τ' (colIndex p.2)) := by
              calc
                τ p.2 = τ (c₀.succAbove (colIndex p.2)) := by rw [hcol_succ]
                _ = Fin.succ (τ' (colIndex p.2)) :=
                  rankLift_succAbove c₀ τ' (colIndex p.2)
            rw [hσ, hτ]
            exact show Fin.succ (σ' (rowIndex p.1)) < Fin.succ (τ' (colIndex p.2)) by
              simpa [Fin.succ] using Nat.succ_lt_succ
                (show (σ' (rowIndex p.1)).val < (τ' (colIndex p.2)).val from hlt')
      · let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 e.1
        let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 e.2
        refine ⟨σ, τ, 0, ?_, ?_, ?_⟩
        · simp [σ]
        · simp [τ]
        · intro p hp hp_ne_e
          have hrow : p.1 = e.1 := by
            by_contra hne
            exact houtside ⟨p, hp, hp_ne_e, hne⟩
          have hcol_ne : p.2 ≠ e.2 := by
            intro hcol
            exact hp_ne_e (Prod.ext hrow hcol)
          have hτ_ne_zero : τ p.2 ≠ 0 := by
            intro hzero
            have hτe : τ e.2 = 0 := by simp [τ]
            have hcol : p.2 = e.2 := τ.injective (hzero.trans hτe.symm)
            exact hcol_ne hcol
          have hτ_pos : 0 < (τ p.2).val := by
            have hval_ne : (τ p.2).val ≠ 0 := by
              intro hval
              exact hτ_ne_zero (Fin.ext hval)
            omega
          rw [hrow]
          change (σ e.1).val < (τ p.2).val
          simp [σ]
          exact hτ_pos































/-!
## Step 1: deletion and shrink in back-diagonal coordinates

For a back-diagonal normalized square `Q`, delete the last row and column `0`.
The retained cell `(i,j)` of the order-`N` problem is `Q i.castSucc j.succ`.
The last symbol is dropped from the symbol type.
-/















/-!
## Smetaniuk's back-diagonal partial square

Given an order-`N` Latin square `L₀`, `smetBackPartial L₀` is the canonical
order-`N + 1` partial square with the new symbol on the back diagonal, `L₀`
below that diagonal, and empty cells above it.
-/















































/-!
## The Smetaniuk switching rectangle

The core construction first turns the first `N` rows into an `N × (N + 1)`
Latin rectangle.  Column `N` is used as the temporary holding column.  When
processing a column `c`, the active rows are the bottom rows `N - c, …, N - 1`.
Swapping in the first active row puts the new symbol on the back diagonal; if
that creates a repeated old symbol in the holding column, the repair follows
the unique row carrying that old symbol.  The reachable-row closure below
packages exactly that repair chain.
-/





























































end ProofsInTheBook.Chapter33

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter33
-/
/- Source module: ProofsInTheBook.Chapter33Ryser -/
section
set_option autoImplicit true


open Finset
open Classical

namespace ProofsInTheBook.Chapter33

/-!
# Ryser's few-elements case for Chapter 33

This file formalizes the book's Lemma 2 route: first conjugate a partial
Latin square by swapping rows and symbols, then complete a row-sparse partial
square by the row-by-row Hall argument and finish the resulting Latin rectangle.
-/







































































































end ProofsInTheBook.Chapter33

end

/- Original source header (imports hoisted):
/-
Chapter 33 (book chapter 32, "Completing Latin squares"): the unconditional
Evans/Smetaniuk completion theorem.

This file only wires together the two halves proved in
`Chapter33Smetaniuk.lean` (the Smetaniuk singleton-element induction,
following the book proof: normalize the unique symbol onto the diagonal,
delete it, induct, and recover it from the back-diagonal extension) and
`Chapter33Ryser.lean` (book Lemma 2: a sparse partial Latin square using at
most `n / 2` symbols completes, by conjugacy and Hall's theorem).
-/
import ProofsInTheBook.Chapter33Smetaniuk
import ProofsInTheBook.Chapter33Ryser
-/
/- Source module: ProofsInTheBook.Chapter33Unconditional -/
section
set_option autoImplicit true


namespace ProofsInTheBook.Chapter33





end ProofsInTheBook.Chapter33

end


set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

theorem solution {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    {a : Fin (N + 1)}
    (hcard : (filledCells P).card ≤ N)
    (hone : SymbolOccursExactlyOnce P a) :
    ∃ rowPerm colPerm symPerm : Equiv.Perm (Fin (N + 1)), ∃ d : Fin (N + 1),
      SmetaniukTriangularNormalized
        (relabelPartial rowPerm colPerm symPerm P) d (Fin.last N) := by
  classical
  rcases hone with ⟨e, hcell_e, huniq⟩
  have he : e ∈ filledCells P := by
    simp [filledCells, hcell_e]
  have hlt : (filledCells P).card < N + 1 := by omega
  obtain ⟨σ, τ, d, hσe, hτe, hstrict⟩ :=
    exists_perm_singleton_diagonal_strictly_above (filledCells P) he hlt
  let symPerm : Equiv.Perm (Fin (N + 1)) := Equiv.swap a (Fin.last N)
  refine ⟨σ.symm, τ.symm, symPerm, d, ?_⟩
  have hrow_old : σ.symm d = e.1 := by
    apply σ.injective
    simp [hσe]
  have hcol_old : τ.symm d = e.2 := by
    apply τ.injective
    simp [hτe]
  have hsym_last : symPerm.symm (Fin.last N) = a := by
    simp [symPerm]
  have hdiag :
      relabelPartial σ.symm τ.symm symPerm P d d = some (Fin.last N) := by
    apply (relabelPartial_eq_some_iff σ.symm τ.symm symPerm P d d
      (Fin.last N)).mpr
    simpa [hrow_old, hcol_old, hsym_last] using hcell_e
  constructor
  · constructor
    · exact hdiag
    · refine ⟨(d, d), hdiag, ?_⟩
      intro ij hij
      have hold :
          P (σ.symm ij.1) (τ.symm ij.2) = some a := by
        have hraw :=
          (relabelPartial_eq_some_iff σ.symm τ.symm symPerm P ij.1 ij.2
            (Fin.last N)).mp hij
        simpa [hsym_last] using hraw
      have hp : (σ.symm ij.1, τ.symm ij.2) = e := huniq _ hold
      apply Prod.ext
      · have hrow : σ.symm ij.1 = e.1 := congrArg Prod.fst hp
        calc
          ij.1 = σ (σ.symm ij.1) := by simp
          _ = σ e.1 := by rw [hrow]
          _ = d := hσe
      · have hcol : τ.symm ij.2 = e.2 := congrArg Prod.snd hp
        calc
          ij.2 = τ (τ.symm ij.2) := by simp
          _ = τ e.2 := by rw [hcol]
          _ = d := hτe
  · intro i j s hcell hs
    have hold :
        P (σ.symm i) (τ.symm j) = some (symPerm.symm s) :=
      (relabelPartial_eq_some_iff σ.symm τ.symm symPerm P i j s).mp hcell
    have hp : (σ.symm i, τ.symm j) ∈ filledCells P := by
      simp [filledCells, hold]
    have hp_ne : (σ.symm i, τ.symm j) ≠ e := by
      intro hp_eq
      have hsym_eq : symPerm.symm s = a := by
        have hsame : some (symPerm.symm s) = some a := by
          rw [← hold]
          simpa [← hp_eq] using hcell_e
        exact Option.some.inj hsame
      have hs_last : s = Fin.last N := by
        calc
          s = symPerm (symPerm.symm s) := by simp
          _ = symPerm a := by rw [hsym_eq]
          _ = Fin.last N := by simp [symPerm]
      exact hs hs_last
    have hlt' := hstrict (σ.symm i, τ.symm j) hp hp_ne
    simpa using hlt'
