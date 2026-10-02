-- Prove2me | solution 1 for ProofsInTheBook.Chapter33.extend_partialLatin_to_exact
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:08:46.302006+00:00
-- url     : https://prove2.me/submissions/a9800895-72d0-44ca-95d8-9d29de6ba34e

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

























































lemma extendsPartial_refl {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) :
    ExtendsPartial P P := by
  intro i j a h
  exact h

lemma extendsPartial_trans {n : ℕ} {P Q R : Fin n → Fin n → Option (Fin n)}
    (hPQ : ExtendsPartial P Q) (hQR : ExtendsPartial Q R) :
    ExtendsPartial P R := by
  intro i j a h
  exact hQR i j a (hPQ i j a h)

lemma extendsPartial_setCell_of_empty {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    {i₀ j₀ a : Fin n} (hempty : P i₀ j₀ = none) :
    ExtendsPartial P (setCell P i₀ j₀ a) := by
  intro i j b hP
  by_cases hcell : i = i₀ ∧ j = j₀
  · rcases hcell with ⟨hi, hj⟩
    subst i
    subst j
    rw [hempty] at hP
    cases hP
  · simp [setCell, hcell, hP]



lemma isPartialLatin_setCell {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    {i₀ j₀ a : Fin n} (hP : IsPartialLatin P) (_hempty : P i₀ j₀ = none)
    (haRow : a ∉ rowSymbols P i₀) (haCol : a ∉ colSymbols P j₀) :
    IsPartialLatin (setCell P i₀ j₀ a) := by
  constructor
  · intro i j₁ j₂ b hb₁ hb₂
    by_cases h₁ : i = i₀ ∧ j₁ = j₀
    · by_cases h₂ : i = i₀ ∧ j₂ = j₀
      · exact h₁.2.trans h₂.2.symm
      · have hi : i = i₀ := h₁.1
        have hj₁ : j₁ = j₀ := h₁.2
        have hab : a = b := Option.some.inj (by simpa [setCell, h₁] using hb₁)
        have hb₂P : P i j₂ = some b := by simpa [setCell, h₂] using hb₂
        have : a ∈ rowSymbols P i₀ := by
          simp [rowSymbols]
          exact ⟨j₂, by simpa [hi, hab] using hb₂P⟩
        exact False.elim (haRow this)
    · by_cases h₂ : i = i₀ ∧ j₂ = j₀
      · have hi : i = i₀ := h₂.1
        have hj₂ : j₂ = j₀ := h₂.2
        have hab : a = b := Option.some.inj (by simpa [setCell, h₂] using hb₂)
        have hb₁P : P i j₁ = some b := by simpa [setCell, h₁] using hb₁
        have : a ∈ rowSymbols P i₀ := by
          simp [rowSymbols]
          exact ⟨j₁, by simpa [hi, hab] using hb₁P⟩
        exact False.elim (haRow this)
      · have hb₁P : P i j₁ = some b := by simpa [setCell, h₁] using hb₁
        have hb₂P : P i j₂ = some b := by simpa [setCell, h₂] using hb₂
        exact hP.1 i j₁ j₂ b hb₁P hb₂P
  · intro i₁ i₂ j b hb₁ hb₂
    by_cases h₁ : i₁ = i₀ ∧ j = j₀
    · by_cases h₂ : i₂ = i₀ ∧ j = j₀
      · exact h₁.1.trans h₂.1.symm
      · have hi₁ : i₁ = i₀ := h₁.1
        have hj : j = j₀ := h₁.2
        have hab : a = b := Option.some.inj (by simpa [setCell, h₁] using hb₁)
        have hb₂P : P i₂ j = some b := by simpa [setCell, h₂] using hb₂
        have : a ∈ colSymbols P j₀ := by
          simp [colSymbols]
          exact ⟨i₂, by simpa [hj, hab] using hb₂P⟩
        exact False.elim (haCol this)
    · by_cases h₂ : i₂ = i₀ ∧ j = j₀
      · have hi₂ : i₂ = i₀ := h₂.1
        have hj : j = j₀ := h₂.2
        have hab : a = b := Option.some.inj (by simpa [setCell, h₂] using hb₂)
        have hb₁P : P i₁ j = some b := by simpa [setCell, h₁] using hb₁
        have : a ∈ colSymbols P j₀ := by
          simp [colSymbols]
          exact ⟨i₁, by simpa [hj, hab] using hb₁P⟩
        exact False.elim (haCol this)
      · have hb₁P : P i₁ j = some b := by simpa [setCell, h₁] using hb₁
        have hb₂P : P i₂ j = some b := by simpa [setCell, h₂] using hb₂
        exact hP.2 i₁ i₂ j b hb₁P hb₂P



lemma filledCells_setCell_of_empty {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i₀ j₀ a : Fin n}
    (hempty : P i₀ j₀ = none) :
    filledCells (setCell P i₀ j₀ a) = insert (i₀, j₀) (filledCells P) := by
  classical
  ext ij
  by_cases hcell : ij = (i₀, j₀)
  · subst ij
    simp [filledCells, setCell, hempty]
  · have hnot : ¬ (ij.1 = i₀ ∧ ij.2 = j₀) := by
      intro h
      exact hcell (Prod.ext h.1 h.2)
    simp [filledCells, setCell, hnot, hcell]

lemma filledCells_setCell_card_of_empty {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i₀ j₀ a : Fin n}
    (hempty : P i₀ j₀ = none) :
    (filledCells (setCell P i₀ j₀ a)).card = (filledCells P).card + 1 := by
  classical
  rw [filledCells_setCell_of_empty P hempty]
  have hnotmem : (i₀, j₀) ∉ filledCells P := by
    simp [filledCells, hempty]
  rw [Finset.card_insert_of_notMem hnotmem]













lemma rowSymbols_card_le_rowCells_card {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (i : Fin n) :
    (rowSymbols P i).card ≤ (rowCells P i).card := by
  classical
  let witness : Fin n → Fin n := fun a =>
    if h : ∃ j, P i j = some a then Classical.choose h else i
  refine Finset.card_le_card_of_injOn (fun a => (i, witness a)) ?_ ?_
  · intro a ha
    have hex : ∃ j, P i j = some a := by simpa [rowSymbols] using ha
    have hcell : P i (witness a) = some a := by
      simpa [witness, hex] using Classical.choose_spec hex
    simp [rowCells, filledCells, hcell]
  · intro a ha b hb hab
    have hexa : ∃ j, P i j = some a := by simpa [rowSymbols] using ha
    have hexb : ∃ j, P i j = some b := by simpa [rowSymbols] using hb
    have hw : witness a = witness b := Prod.mk.inj hab |>.2
    have hcella : P i (witness a) = some a := by
      simpa [witness, hexa] using Classical.choose_spec hexa
    have hcellb : P i (witness b) = some b := by
      simpa [witness, hexb] using Classical.choose_spec hexb
    have hsome : some a = some b := by
      rw [← hcella, hw, hcellb]
    exact Option.some.inj hsome

lemma colSymbols_card_le_colCells_card {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (j : Fin n) :
    (colSymbols P j).card ≤ (colCells P j).card := by
  classical
  let witness : Fin n → Fin n := fun a =>
    if h : ∃ i, P i j = some a then Classical.choose h else j
  refine Finset.card_le_card_of_injOn (fun a => (witness a, j)) ?_ ?_
  · intro a ha
    have hex : ∃ i, P i j = some a := by simpa [colSymbols] using ha
    have hcell : P (witness a) j = some a := by
      simpa [witness, hex] using Classical.choose_spec hex
    simp [colCells, filledCells, hcell]
  · intro a ha b hb hab
    have hexa : ∃ i, P i j = some a := by simpa [colSymbols] using ha
    have hexb : ∃ i, P i j = some b := by simpa [colSymbols] using hb
    have hw : witness a = witness b := Prod.mk.inj hab |>.1
    have hcella : P (witness a) j = some a := by
      simpa [witness, hexa] using Classical.choose_spec hexa
    have hcellb : P (witness b) j = some b := by
      simpa [witness, hexb] using Classical.choose_spec hexb
    have hsome : some a = some b := by
      rw [← hcella, hw, hcellb]
    exact Option.some.inj hsome

lemma rowCells_disjoint_colCells_of_empty {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i₀ j₀ : Fin n}
    (hempty : P i₀ j₀ = none) :
    Disjoint (rowCells P i₀) (colCells P j₀) := by
  rw [Finset.disjoint_left]
  intro ij hijRow hijCol
  have hfilled : (P ij.1 ij.2).isSome := by
    simpa [rowCells, filledCells] using (Finset.mem_filter.mp hijRow).1
  have hi : ij.1 = i₀ := (Finset.mem_filter.mp hijRow).2
  have hj : ij.2 = j₀ := (Finset.mem_filter.mp hijCol).2
  rw [hi, hj, hempty] at hfilled
  simp at hfilled

lemma rowCells_union_colCells_card_le_filledCells {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i₀ j₀ : Fin n) :
    ((rowCells P i₀) ∪ (colCells P j₀)).card ≤ (filledCells P).card := by
  exact Finset.card_le_card (by
    intro ij hij
    rcases Finset.mem_union.mp hij with hijRow | hijCol
    · exact (Finset.mem_filter.mp hijRow).1
    · exact (Finset.mem_filter.mp hijCol).1)

lemma row_col_symbols_card_le_filledCells_of_empty {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    {i₀ j₀ : Fin n} (hempty : P i₀ j₀ = none) :
    ((rowSymbols P i₀) ∪ (colSymbols P j₀)).card ≤ (filledCells P).card := by
  classical
  have hrow := rowSymbols_card_le_rowCells_card P i₀
  have hcol := colSymbols_card_le_colCells_card P j₀
  have hsym_union :
      ((rowSymbols P i₀) ∪ (colSymbols P j₀)).card ≤
        (rowSymbols P i₀).card + (colSymbols P j₀).card :=
    Finset.card_union_le _ _
  have hcell_sum :
      (rowCells P i₀).card + (colCells P j₀).card =
        ((rowCells P i₀) ∪ (colCells P j₀)).card := by
    rw [Finset.card_union_of_disjoint (rowCells_disjoint_colCells_of_empty P hempty)]
  have hcell_union := rowCells_union_colCells_card_le_filledCells P i₀ j₀
  calc
    ((rowSymbols P i₀) ∪ (colSymbols P j₀)).card
        ≤ (rowSymbols P i₀).card + (colSymbols P j₀).card := hsym_union
    _ ≤ (rowCells P i₀).card + (colCells P j₀).card := Nat.add_le_add hrow hcol
    _ = ((rowCells P i₀) ∪ (colCells P j₀)).card := hcell_sum
    _ ≤ (filledCells P).card := hcell_union

lemma exists_symbol_not_row_col_of_filledCells_le {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    {i₀ j₀ : Fin n} (hempty : P i₀ j₀ = none)
    (hfilled_le : (filledCells P).card ≤ n - 2) :
    ∃ a : Fin n, a ∉ rowSymbols P i₀ ∧ a ∉ colSymbols P j₀ := by
  classical
  let U := (rowSymbols P i₀) ∪ (colSymbols P j₀)
  have hU_le : U.card ≤ n - 2 := by
    exact le_trans (row_col_symbols_card_le_filledCells_of_empty hempty) hfilled_le
  have hU_lt : U.card < n := by
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i₀.val) i₀.isLt
    omega
  by_contra hnone
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ U := by
    intro a _ha
    by_cases haU : a ∈ U
    · exact haU
    · have hrow : a ∉ rowSymbols P i₀ := by
        intro h
        exact haU (Finset.mem_union.mpr (Or.inl h))
      have hcol : a ∉ colSymbols P j₀ := by
        intro h
        exact haU (Finset.mem_union.mpr (Or.inr h))
      exact False.elim (hnone ⟨a, hrow, hcol⟩)
  have hn_le : n ≤ U.card := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ U.card := Finset.card_le_card hsub
  omega

lemma exists_empty_cell_of_filledCells_lt_pred {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hcard_lt : (filledCells P).card < n - 1) :
    ∃ i j, P i j = none := by
  classical
  have hnpos : 0 < n := by omega
  have hnn : n ≤ n * n := by
    nth_rewrite 1 [← Nat.mul_one n]
    exact Nat.mul_le_mul_left n (Nat.succ_le_of_lt hnpos)
  have hlt_univ : (filledCells P).card < (Finset.univ : Finset (Fin n × Fin n)).card := by
    have hcard_univ : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by simp
    rw [hcard_univ]
    exact lt_of_lt_of_le hcard_lt (le_trans (Nat.sub_le n 1) hnn)
  by_contra hnone
  push Not at hnone
  have hfull : filledCells P = (Finset.univ : Finset (Fin n × Fin n)) := by
    ext ij
    simp [filledCells]
    cases hcell : P ij.1 ij.2 with
    | none =>
        exact False.elim (hnone ij.1 ij.2 hcell)
    | some a =>
        simp
  have hnot_lt : ¬ (filledCells P).card < (Finset.univ : Finset (Fin n × Fin n)).card := by
    rw [hfull]
    exact lt_irrefl _
  exact hnot_lt hlt_univ

/--
If a partial Latin square has fewer than `n - 1` entries, one more entry can be
added while preserving the partial Latin property.

This formalizes the easy final sentence in Smetaniuk's proof: the case
`|P| < n - 1` can be reduced to the exact `|P| = n - 1` case by adding
entries one at a time.
-/
theorem extend_partialLatin_one {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) (hcard_lt : (filledCells P).card < n - 1) :
    ∃ Q : Fin n → Fin n → Option (Fin n),
      IsPartialLatin Q ∧ ExtendsPartial P Q ∧
        (filledCells Q).card = (filledCells P).card + 1 := by
  classical
  obtain ⟨i₀, j₀, hempty⟩ := exists_empty_cell_of_filledCells_lt_pred P hcard_lt
  have hfilled_le : (filledCells P).card ≤ n - 2 := by omega
  obtain ⟨a, haRow, haCol⟩ :=
    exists_symbol_not_row_col_of_filledCells_le hempty hfilled_le
  refine ⟨setCell P i₀ j₀ a, ?_, ?_, ?_⟩
  · exact isPartialLatin_setCell hP hempty haRow haCol
  · exact extendsPartial_setCell_of_empty P hempty
  · exact filledCells_setCell_card_of_empty P hempty





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

theorem solution {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ Q : Fin n → Fin n → Option (Fin n),
      IsPartialLatin Q ∧ ExtendsPartial P Q ∧ (filledCells Q).card = n - 1 := by
  classical
  let d₀ := n - 1 - (filledCells P).card
  have hmain :
      ∀ d : ℕ,
        (∀ e < d,
          ∀ R : Fin n → Fin n → Option (Fin n),
            IsPartialLatin R →
              (filledCells R).card ≤ n - 1 →
                e = n - 1 - (filledCells R).card →
                  ∃ Q : Fin n → Fin n → Option (Fin n),
                    IsPartialLatin Q ∧ ExtendsPartial R Q ∧
                      (filledCells Q).card = n - 1) →
        ∀ R : Fin n → Fin n → Option (Fin n),
          IsPartialLatin R →
            (filledCells R).card ≤ n - 1 →
              d = n - 1 - (filledCells R).card →
                ∃ Q : Fin n → Fin n → Option (Fin n),
                  IsPartialLatin Q ∧ ExtendsPartial R Q ∧
                    (filledCells Q).card = n - 1 := by
    intro d ih R hR hR_le hd
    by_cases hexact : (filledCells R).card = n - 1
    · refine ⟨R, hR, extendsPartial_refl R, hexact⟩
    · have hlt : (filledCells R).card < n - 1 := lt_of_le_of_ne hR_le hexact
      obtain ⟨R₁, hR₁, hRR₁, hcard₁⟩ := extend_partialLatin_one hR hlt
      have hR₁_le : (filledCells R₁).card ≤ n - 1 := by omega
      let e := n - 1 - (filledCells R₁).card
      have heq : e = n - 1 - (filledCells R₁).card := rfl
      have he_lt : e < d := by
        subst d
        dsimp [e]
        omega
      obtain ⟨Q, hQ, hR₁Q, hQcard⟩ := ih e he_lt R₁ hR₁ hR₁_le heq
      exact ⟨Q, hQ, extendsPartial_trans hRR₁ hR₁Q, hQcard⟩
  let motive := fun d : ℕ =>
    ∀ R : Fin n → Fin n → Option (Fin n),
      IsPartialLatin R →
        (filledCells R).card ≤ n - 1 →
          d = n - 1 - (filledCells R).card →
            ∃ Q : Fin n → Fin n → Option (Fin n),
              IsPartialLatin Q ∧ ExtendsPartial R Q ∧ (filledCells Q).card = n - 1
  exact (Nat.strong_induction_on (p := motive) d₀ hmain) P hP hfilled_le rfl
