-- Prove2me | solution 1 for ProofsInTheBook.Chapter33.exists_symbol_occursExactlyOnce_of_many_used
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:08:44.175142+00:00
-- url     : https://prove2.me/submissions/df8f5318-b20d-4f87-8444-77700c0af4a9

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





































































private lemma exists_two_cells_of_used_not_once {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} {a : Fin n}
    (ha : a ∈ usedSymbols P) (hnot : ¬ SymbolOccursExactlyOnce P a) :
    ∃ ij₀ ij₁ : Fin n × Fin n,
      ij₀ ∈ filledCells P ∧ ij₁ ∈ filledCells P ∧
        P ij₀.1 ij₀.2 = some a ∧ P ij₁.1 ij₁.2 = some a ∧ ij₀ ≠ ij₁ := by
  classical
  rcases (by simpa [usedSymbols] using ha) with ⟨i₀, j₀, hcell₀⟩
  let ij₀ : Fin n × Fin n := (i₀, j₀)
  have hmem₀ : ij₀ ∈ filledCells P := by
    simp [ij₀, filledCells, hcell₀]
  have hsecond : ∃ ij₁ : Fin n × Fin n,
      P ij₁.1 ij₁.2 = some a ∧ ij₁ ≠ ij₀ := by
    by_contra hnone
    have hall : ∀ ij : Fin n × Fin n,
        P ij.1 ij.2 = some a → ij = ij₀ := by
      intro ij hcell
      by_contra hne
      exact hnone ⟨ij, hcell, hne⟩
    exact hnot ⟨ij₀, by simpa [ij₀] using hcell₀, hall⟩
  rcases hsecond with ⟨ij₁, hcell₁, hne₁⟩
  have hmem₁ : ij₁ ∈ filledCells P := by
    simp [filledCells, hcell₁]
  exact ⟨ij₀, ij₁, hmem₀, hmem₁, by simpa [ij₀] using hcell₀, hcell₁, hne₁.symm⟩























































































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

theorem solution {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hcard : (filledCells P).card ≤ n - 1)
    (hmany : n < 2 * (usedSymbols P).card) :
    ∃ a : Fin n, SymbolOccursExactlyOnce P a := by
  classical
  by_contra hnone
  let U : Finset (Fin n) := usedSymbols P
  have hnot_once : ∀ a : Fin n, a ∈ U → ¬ SymbolOccursExactlyOnce P a := by
    intro a ha hone
    exact hnone ⟨a, hone⟩
  have htwo : ∀ a : Fin n, a ∈ U →
      ∃ ij₀ ij₁ : Fin n × Fin n,
        ij₀ ∈ filledCells P ∧ ij₁ ∈ filledCells P ∧
          P ij₀.1 ij₀.2 = some a ∧ P ij₁.1 ij₁.2 = some a ∧ ij₀ ≠ ij₁ := by
    intro a ha
    exact exists_two_cells_of_used_not_once ha (hnot_once a ha)
  choose first second hfirst using htwo
  let D : Finset (Fin n × Fin 2) := U ×ˢ (Finset.univ : Finset (Fin 2))
  let f : Fin n × Fin 2 → Fin n × Fin n := fun p =>
    if ha : p.1 ∈ U then
      if p.2 = 0 then first p.1 ha else second p.1 ha
    else
      (p.1, p.1)
  have hf_mem : ∀ p : Fin n × Fin 2, p ∈ D → f p ∈ filledCells P := by
    intro p hp
    have ha : p.1 ∈ U := (Finset.mem_product.mp hp).1
    by_cases hb : p.2 = 0
    · have hf : f p = first p.1 ha := by
        simp [f, ha, hb]
      simpa [hf] using (hfirst p.1 ha).1
    · have hf : f p = second p.1 ha := by
        simp [f, ha, hb]
      simpa [hf] using (hfirst p.1 ha).2.1
  have hf_sym : ∀ p : Fin n × Fin 2, p ∈ D →
      P (f p).1 (f p).2 = some p.1 := by
    intro p hp
    have ha : p.1 ∈ U := (Finset.mem_product.mp hp).1
    by_cases hb : p.2 = 0
    · have hf : f p = first p.1 ha := by
        simp [f, ha, hb]
      simpa [hf] using (hfirst p.1 ha).2.2.1
    · have hf : f p = second p.1 ha := by
        simp [f, ha, hb]
      simpa [hf] using (hfirst p.1 ha).2.2.2.1
  have hf_inj : ∀ x ∈ D, ∀ y ∈ D, f x = f y → x = y := by
    intro x hx y hy hxy
    have hxcell := hf_sym x hx
    have hycell := hf_sym y hy
    have hsym : x.1 = y.1 := by
      exact Option.some.inj (by rw [← hxcell, hxy, hycell])
    cases x with
    | mk ax bx =>
      cases y with
      | mk ay byy =>
        have hsym' : ax = ay := by
          simpa using hsym
        subst ay
        have hax : ax ∈ U := (Finset.mem_product.mp hx).1
        have hfirst_ne_second : first ax hax ≠ second ax hax :=
          (hfirst ax hax).2.2.2.2
        fin_cases bx <;> fin_cases byy <;> simp [f, hax] at hxy ⊢
        · exact False.elim (hfirst_ne_second hxy)
        · exact False.elim (hfirst_ne_second hxy.symm)
  have hle_card : D.card ≤ (filledCells P).card :=
    Finset.card_le_card_of_injOn f hf_mem hf_inj
  have hDcard : D.card = 2 * U.card := by
    simp [D, Nat.mul_comm]
  have htwo_le : 2 * (usedSymbols P).card ≤ (filledCells P).card := by
    simpa [U, hDcard] using hle_card
  have hlt_filled : (filledCells P).card < n := by omega
  omega
