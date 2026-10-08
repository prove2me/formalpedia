-- Prove2me | solution 1 for ProofsInTheBook.Chapter33.smetMainPartial_extends_of_keepLastShrink_completion
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:09:11.42801+00:00
-- url     : https://prove2.me/submissions/3c6bc8c3-0eaf-45e4-827a-68df5c0936ec

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







































































































lemma mainDiagonalNewSymbol_cell_eq {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} {d newSym i j : Fin n}
    (hmain : MainDiagonalNewSymbol P d newSym)
    (hcell : P i j = some newSym) : i = d ∧ j = d := by
  rcases hmain with ⟨hdiag, huniq⟩
  rcases huniq with ⟨ij₀, hij₀, huniq₀⟩
  have hij : (i, j) = ij₀ := huniq₀ (i, j) hcell
  have hdd : (d, d) = ij₀ := huniq₀ (d, d) hdiag
  have hp : (i, j) = (d, d) := hij.trans hdd.symm
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩































@[simp] lemma dropLastSymbol_castSucc {N : ℕ} (a : Fin N) :
    dropLastSymbol (Fin.castSucc a : Fin (N + 1)) = some a := by
  unfold dropLastSymbol
  have h : (Fin.castSucc a : Fin (N + 1)).val < N := by
    simp [Fin.castSucc]
  simp

lemma dropLastSymbol_eq_some {N : ℕ} {a : Fin (N + 1)} {b : Fin N}
    (h : dropLastSymbol a = some b) : a = Fin.castSucc b := by
  unfold dropLastSymbol at h
  by_cases ha : a.val < N
  · simp [ha] at h
    have hb : (⟨a.val, ha⟩ : Fin N) = b := h
    exact Fin.ext (by simpa [Fin.castSucc] using congrArg Fin.val hb)
  · simp [ha] at h



@[simp] lemma reverseColumnsPartial_eq {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i j : Fin n) :
    reverseColumnsPartial P i j = P i (Fin.rev j) := by
  simp [reverseColumnsPartial, relabelPartial]















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



lemma smetBackPartial_back_diagonal {N : ℕ} (L₀ : Fin N → Fin N → Fin N)
    {i j : Fin (N + 1)} (hdiag : i.val + j.val = N) :
    smetBackPartial L₀ i j = some (Fin.last N) := by
  simp [smetBackPartial, hdiag]















lemma smetMainPartial_diagonal {N : ℕ} (L₀ : Fin N → Fin N → Fin N)
    (i : Fin (N + 1)) :
    smetMainPartial L₀ i i = some (Fin.last N) := by
  rw [smetMainPartial, reverseColumnsPartial_eq]
  apply smetBackPartial_back_diagonal
  simp [Fin.rev]
  have hi : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
  omega











lemma smetMainKeepLastShrink_eq_some_iff {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)))
    (i j : Fin N) (a : Fin N) :
    smetMainKeepLastShrink P i j = some a ↔
      P (Fin.castSucc i) (Fin.rev (Fin.castSucc j)) = some (Fin.castSucc a) := by
  constructor
  · intro h
    unfold smetMainKeepLastShrink at h
    cases hP : P (Fin.castSucc i) (Fin.rev (Fin.castSucc j)) with
    | none =>
        simp [hP] at h
    | some b =>
        simp [hP] at h
        have hb : b = Fin.castSucc a := dropLastSymbol_eq_some h
        simp [hb]
  · intro h
    simp [smetMainKeepLastShrink, h]











private lemma fin_ne_last_iff_val_lt {N : ℕ} {a : Fin (N + 1)} :
    a ≠ Fin.last N ↔ a.val < N := by
  constructor
  · intro h
    have hle : a.val ≤ N := Nat.lt_succ_iff.mp a.isLt
    by_contra hlt
    have hge : N ≤ a.val := Nat.le_of_not_gt hlt
    exact h (Fin.ext (le_antisymm hle hge))
  · intro hlt h
    have hv : a.val = N := by simpa [Fin.last] using congrArg Fin.val h
    omega



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

lemma solution {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    {L₀ : Fin N → Fin N → Fin N}
    (hL₀ : Completes (smetMainKeepLastShrink P) L₀)
    {d : Fin (N + 1)}
    (hnorm : SmetaniukTriangularNormalized P d (Fin.last N)) :
    ExtendsPartial P (smetMainPartial L₀) := by
  intro i j a hcell
  rcases hnorm with ⟨hmain, htri⟩
  by_cases haLast : a = Fin.last N
  · subst a
    have hij := mainDiagonalNewSymbol_cell_eq hmain hcell
    rcases hij with ⟨hi, hj⟩
    subst i
    subst j
    exact smetMainPartial_diagonal L₀ d
  · have hlt : i < j := htri i j a hcell haLast
    have hi_ltN : i.val < N := by
      have hj_le : j.val ≤ N := Nat.lt_succ_iff.mp j.isLt
      have hltVal : i.val < j.val := hlt
      omega
    have hj_pos : 0 < j.val := by
      have hltVal : i.val < j.val := hlt
      omega
    have ha_ltN : a.val < N := (fin_ne_last_iff_val_lt.mp haLast)
    let ii : Fin N := ⟨i.val, hi_ltN⟩
    let kk : Fin N := ⟨N - j.val, by omega⟩
    let aa : Fin N := ⟨a.val, ha_ltN⟩
    have hi_cast : (Fin.castSucc ii : Fin (N + 1)) = i := by
      exact Fin.ext rfl
    have ha_cast : (Fin.castSucc aa : Fin (N + 1)) = a := by
      exact Fin.ext rfl
    have hj_repr : Fin.rev (Fin.castSucc kk : Fin (N + 1)) = j := by
      apply Fin.ext
      simp [Fin.rev, kk]
      have hj_le : j.val ≤ N := Nat.lt_succ_iff.mp j.isLt
      omega
    have hsmall :
        smetMainKeepLastShrink P ii kk = some aa := by
      apply (smetMainKeepLastShrink_eq_some_iff P ii kk aa).mpr
      simpa [hi_cast, hj_repr, ha_cast] using hcell
    have hLcell : L₀ ii kk = aa := hL₀.2 ii kk aa hsmall
    have hrev_j : Fin.rev j = (Fin.castSucc kk : Fin (N + 1)) := by
      rw [← hj_repr]
      simp
    have hback_lt : i.val + (Fin.rev j).val < N := by
      have hrev_val : (Fin.rev j).val = N - j.val := by simp [Fin.rev]
      have hltVal : i.val < j.val := hlt
      rw [hrev_val]
      omega
    have hback_ne : i.val + (Fin.rev j).val ≠ N := by omega
    have hii : (⟨i.val, by omega⟩ : Fin N) = ii := by
      exact Fin.ext rfl
    have hsum_lt : i.val + kk.val < N := by
      simpa [hrev_j] using hback_lt
    have hsum_ne : i.val + kk.val ≠ N := by omega
    simp [smetMainPartial, smetBackPartial, hsum_ne, hsum_lt, hLcell,
      hrev_j, hii, ha_cast]
