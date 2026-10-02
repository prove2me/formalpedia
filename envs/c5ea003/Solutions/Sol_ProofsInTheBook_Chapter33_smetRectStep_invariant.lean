-- Prove2me | solution 1 for ProofsInTheBook.Chapter33.smetRectStep_invariant
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:09:13.915783+00:00
-- url     : https://prove2.me/submissions/d0394516-bba2-4317-8627-8045b1ce1a5b

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









































































































lemma fin_castSucc_ne_last {N : ℕ} (i : Fin N) :
    (Fin.castSucc i : Fin (N + 1)) ≠ Fin.last N := by
  intro h
  have hv : i.val = N := by
    simpa [Fin.castSucc, Fin.last] using congrArg Fin.val h
  exact (Nat.ne_of_lt i.isLt) hv



















































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



lemma switchReach_active {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start i : Fin N}
    (hstart : active start) (h : switchReach R c active start i) :
    active i := by
  induction h with
  | start => exact hstart
  | step _ hr _ _ => exact hr

lemma switchReach_forward {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start q r : Fin N}
    (hq : switchReach R c active start q) (hr : active r)
    (hval : R r (Fin.last N) = R q c) :
    switchReach R c active start r :=
  switchReach.step hq hr hval

lemma switchReach_backward {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start i q : Fin N}
    (hcol : Function.Injective fun r : Fin N => R r c)
    (hstartLast : R start (Fin.last N) = Fin.last N)
    (hcol_ne_last : ∀ r : Fin N, R r c ≠ Fin.last N)
    (hi : switchReach R c active start i)
    (hval : R i (Fin.last N) = R q c) :
    switchReach R c active start q := by
  induction hi with
  | start =>
      exfalso
      exact hcol_ne_last q (by simpa [hstartLast] using hval.symm)
  | step hp hr hstep ih =>
      rename_i q₀ r₀
      have hq : q₀ = q := hcol (hstep.symm.trans hval)
      simpa [hq] using hp



lemma smetSwitchColumn_row_injective {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start : Fin N}
    (hrow : ∀ i : Fin N, Function.Injective (R i))
    (_hc : c ≠ Fin.last N) :
    ∀ i : Fin N, Function.Injective (smetSwitchColumn R c active start i) := by
  intro i j₁ j₂ h
  unfold smetSwitchColumn at h
  by_cases hi : switchReach R c active start i
  · simp [hi] at h
    have hswap :
        (fun j : Fin (N + 1) =>
          if j = c then R i (Fin.last N)
          else if j = Fin.last N then R i c
          else R i j) =
        fun j : Fin (N + 1) => R i ((Equiv.swap c (Fin.last N)) j) := by
      funext j
      by_cases hjc : j = c
      · subst j
        simp
      · by_cases hjl : j = Fin.last N
        · subst j
          simp [hjc]
        · simp [hjc, hjl, Equiv.swap_apply_of_ne_of_ne hjc hjl]
    have h' : R i ((Equiv.swap c (Fin.last N)) j₁) =
        R i ((Equiv.swap c (Fin.last N)) j₂) := by
      exact (congrFun hswap j₁).symm.trans (h.trans (congrFun hswap j₂))
    exact (Equiv.swap c (Fin.last N)).injective ((hrow i) h')
  · simp [hi] at h
    exact hrow i h

lemma smetSwitchColumn_col_ne_injective {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c d : Fin (N + 1)}
    {active : Fin N → Prop} {start : Fin N}
    (hdc : d ≠ c) (hdl : d ≠ Fin.last N)
    (hcol : Function.Injective fun i : Fin N => R i d) :
    Function.Injective fun i : Fin N => smetSwitchColumn R c active start i d := by
  intro i₁ i₂ h
  unfold smetSwitchColumn at h
  by_cases h₁ : switchReach R c active start i₁ <;>
    by_cases h₂ : switchReach R c active start i₂ <;>
      simp [h₁, h₂, hdc, hdl] at h
  all_goals exact hcol h

lemma smetSwitchColumn_col_c_injective {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start : Fin N}
    (hcol : Function.Injective fun i : Fin N => R i c)
    (hlastActive :
      ∀ i₁ i₂ : Fin N, active i₁ → active i₂ →
        R i₁ (Fin.last N) = R i₂ (Fin.last N) → i₁ = i₂)
    (hstartActive : active start)
    (hstartLast : R start (Fin.last N) = Fin.last N)
    (hcol_ne_last : ∀ i : Fin N, R i c ≠ Fin.last N) :
    Function.Injective fun i : Fin N => smetSwitchColumn R c active start i c := by
  intro i₁ i₂ h
  unfold smetSwitchColumn at h
  by_cases h₁ : switchReach R c active start i₁
  · by_cases h₂ : switchReach R c active start i₂
    · simp [h₁, h₂] at h
      exact hlastActive i₁ i₂
        (switchReach_active hstartActive h₁)
        (switchReach_active hstartActive h₂) h
    · simp [h₁, h₂] at h
      have h₂reach :
          switchReach R c active start i₂ :=
        switchReach_backward hcol hstartLast hcol_ne_last h₁ h
      exact False.elim (h₂ h₂reach)
  · by_cases h₂ : switchReach R c active start i₂
    · simp [h₁, h₂] at h
      have h₁reach :
          switchReach R c active start i₁ :=
        switchReach_backward hcol hstartLast hcol_ne_last h₂ h.symm
      exact False.elim (h₁ h₁reach)
    · simp [h₁, h₂] at h
      exact hcol h

lemma smetSwitchColumn_last_active_injective {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start : Fin N}
    (hc : c ≠ Fin.last N)
    (hcol : Function.Injective fun i : Fin N => R i c)
    (hlastActive :
      ∀ i₁ i₂ : Fin N, active i₁ → active i₂ →
        R i₁ (Fin.last N) = R i₂ (Fin.last N) → i₁ = i₂) :
    ∀ i₁ i₂ : Fin N, active i₁ → active i₂ →
      smetSwitchColumn R c active start i₁ (Fin.last N) =
        smetSwitchColumn R c active start i₂ (Fin.last N) →
          i₁ = i₂ := by
  intro i₁ i₂ hi₁ hi₂ h
  have hlast_ne_c : Fin.last N ≠ c := fun hEq => hc hEq.symm
  unfold smetSwitchColumn at h
  by_cases h₁ : switchReach R c active start i₁
  · by_cases h₂ : switchReach R c active start i₂
    · simp [h₁, h₂, hlast_ne_c] at h
      exact hcol h
    · simp [h₁, h₂, hlast_ne_c] at h
      have h₂reach :
          switchReach R c active start i₂ :=
        switchReach_forward h₁ hi₂ h.symm
      exact False.elim (h₂ h₂reach)
  · by_cases h₂ : switchReach R c active start i₂
    · simp [h₁, h₂, hlast_ne_c] at h
      have h₁reach :
          switchReach R c active start i₁ :=
        switchReach_forward h₂ hi₁ h
      exact False.elim (h₁ h₁reach)
    · simp [h₁, h₂] at h
      exact hlastActive i₁ i₂ hi₁ hi₂ h











































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

lemma solution {N t : ℕ}
    {L₀ : Fin N → Fin N → Fin N}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)}
    (ht : t + 1 < N)
    (inv : SmetRectStageInvariant L₀ t R) :
    SmetRectStageInvariant L₀ (t + 1) (smetRectStep R t) := by
  let c : Fin (N + 1) := ⟨t + 1, by omega⟩
  let active : Fin N → Prop := fun i => N - (t + 1) ≤ i.val
  let start : Fin N := ⟨N - (t + 1), by omega⟩
  have hstep :
      smetRectStep R t = smetSwitchColumn R c active start := by
    unfold smetRectStep
    simp [ht, c, active, start]
  rw [hstep]
  have hc_ltN : c.val < N := by
    dsimp [c]
    omega
  have hc_ne_last : c ≠ Fin.last N := by
    intro h
    have hv : c.val = N := by simpa [Fin.last] using congrArg Fin.val h
    dsimp [c] at hv
    omega
  have hstartActive : active start := by
    dsimp [active, start]
    omega
  have hstartLast : R start (Fin.last N) = Fin.last N := by
    exact inv.last_unactive_new start (by dsimp [start]; omega)
  have hcolC : Function.Injective fun i : Fin N => R i c :=
    inv.col_inj c hc_ltN
  have hcol_ne_last : ∀ i : Fin N, R i c ≠ Fin.last N := by
    intro i
    have hval : R i c = Fin.castSucc (L₀ i ⟨c.val, hc_ltN⟩) :=
      inv.unprocessed i c (by dsimp [c]; omega) hc_ltN
    rw [hval]
    exact fin_castSucc_ne_last _
  have oldLast_ne_last :
      ∀ i : Fin N, N - t ≤ i.val → R i (Fin.last N) ≠ Fin.last N := by
    intro i hiOld hlast
    let d : Fin (N + 1) := ⟨N - i.val, by omega⟩
    have hdiag : R i d = Fin.last N := by
      simpa [d] using inv.diag_active i hiOld
    have hd_eq_last : d = Fin.last N := inv.row_inj i (by rw [hdiag, hlast])
    have hv : N - i.val = N := by
      simpa [d, Fin.last] using congrArg Fin.val hd_eq_last
    have hi_lt : i.val < N := i.isLt
    omega
  have hlastActiveBefore :
      ∀ i₁ i₂ : Fin N, active i₁ → active i₂ →
        R i₁ (Fin.last N) = R i₂ (Fin.last N) → i₁ = i₂ := by
    intro i₁ i₂ hi₁ hi₂ hlastEq
    have hNt : N - t = N - (t + 1) + 1 := by omega
    by_cases h₁old : N - t ≤ i₁.val
    · by_cases h₂old : N - t ≤ i₂.val
      · exact inv.last_active_inj i₁ i₂ h₁old h₂old hlastEq
      · have hi₂start : i₂ = start := Fin.ext (by
          have hi₂lt : i₂.val < N - t := Nat.lt_of_not_ge h₂old
          have hi₂le : i₂.val ≤ N - (t + 1) := by omega
          exact le_antisymm hi₂le hi₂)
        subst i₂
        have hbad : R i₁ (Fin.last N) = Fin.last N := by
          simpa [hstartLast] using hlastEq
        exact False.elim (oldLast_ne_last i₁ h₁old hbad)
    · have hi₁start : i₁ = start := Fin.ext (by
        have hi₁lt : i₁.val < N - t := Nat.lt_of_not_ge h₁old
        have hi₁le : i₁.val ≤ N - (t + 1) := by omega
        exact le_antisymm hi₁le hi₁)
      subst i₁
      by_cases h₂old : N - t ≤ i₂.val
      · have hbad : R i₂ (Fin.last N) = Fin.last N := by
          simpa [hstartLast] using hlastEq.symm
        exact False.elim (oldLast_ne_last i₂ h₂old hbad)
      · have hi₂start : i₂ = start := Fin.ext (by
          have hi₂lt : i₂.val < N - t := Nat.lt_of_not_ge h₂old
          have hi₂le : i₂.val ≤ N - (t + 1) := by omega
          exact le_antisymm hi₂le hi₂)
        exact hi₂start.symm
  constructor
  · exact smetSwitchColumn_row_injective inv.row_inj hc_ne_last
  · intro j hj
    by_cases hjc : j = c
    · subst j
      exact smetSwitchColumn_col_c_injective hcolC hlastActiveBefore
        hstartActive hstartLast hcol_ne_last
    · have hjlast : j ≠ Fin.last N := by
        intro hjlast
        have hv : j.val = N := by simpa [Fin.last] using congrArg Fin.val hjlast
        omega
      exact smetSwitchColumn_col_ne_injective hjc hjlast (inv.col_inj j hj)
  · exact smetSwitchColumn_last_active_injective hc_ne_last hcolC hlastActiveBefore
  · intro i hi
    have hnotActive : ¬ active i := by
      intro ha
      dsimp [active] at ha
      omega
    have hnotReach : ¬ switchReach R c active start i := by
      intro hr
      exact hnotActive (switchReach_active hstartActive hr)
    unfold smetSwitchColumn
    simp [hnotReach, inv.last_unactive_new i (by omega)]
  · intro i j htj hj
    have hjc : j ≠ c := by
      intro h
      subst j
      dsimp [c] at htj
      omega
    have hjlast : j ≠ Fin.last N := by
      intro h
      have hv : j.val = N := by simpa [Fin.last] using congrArg Fin.val h
      omega
    unfold smetSwitchColumn
    by_cases hr : switchReach R c active start i
    · simp [hr, hjc, hjlast, inv.unprocessed i j (by omega) hj]
    · simp [hr, inv.unprocessed i j (by omega) hj]
  · intro i j hj hij
    have hjlast : j ≠ Fin.last N := by
      intro h
      have hv : j.val = N := by simpa [Fin.last] using congrArg Fin.val h
      omega
    by_cases hjc : j = c
    · subst j
      have hnotActive : ¬ active i := by
        intro ha
        have hsubadd : N - (t + 1) + (t + 1) = N :=
          Nat.sub_add_cancel (by omega)
        dsimp [active, c] at ha
        have hge : N ≤ i.val + (t + 1) := by
          calc
            N = N - (t + 1) + (t + 1) := hsubadd.symm
            _ ≤ i.val + (t + 1) := Nat.add_le_add_right ha (t + 1)
        have hlt : i.val + (t + 1) < N := by
          simpa [c] using hij
        omega
      have hnotReach : ¬ switchReach R c active start i := by
        intro hr
        exact hnotActive (switchReach_active hstartActive hr)
      unfold smetSwitchColumn
      simp [hnotReach, inv.required_old i c hc_ltN (by simpa [c] using hij)]
    · unfold smetSwitchColumn
      by_cases hr : switchReach R c active start i
      · simp [hr, hjc, hjlast, inv.required_old i j hj hij]
      · simp [hr, inv.required_old i j hj hij]
  · intro i hi
    let d : Fin (N + 1) := ⟨N - i.val, by omega⟩
    change smetSwitchColumn R c active start i d = Fin.last N
    by_cases hiOld : N - t ≤ i.val
    · have hd_ne_c : d ≠ c := by
        intro hdc
        have hv : N - i.val = t + 1 := by
          simpa [d, c] using congrArg Fin.val hdc
        omega
      have hd_ne_last : d ≠ Fin.last N := by
        intro hdl
        have hv : N - i.val = N := by
          simpa [d, Fin.last] using congrArg Fin.val hdl
        have hi_lt : i.val < N := i.isLt
        omega
      have hdiag : R i d = Fin.last N := by
        simpa [d] using inv.diag_active i hiOld
      unfold smetSwitchColumn
      by_cases hr : switchReach R c active start i
      · simp [hr, hd_ne_c, hd_ne_last, hdiag]
      · simp [hr, hdiag]
    · have histart : i = start := Fin.ext (by
        have hNt : N - t = N - (t + 1) + 1 := by omega
        have hilt : i.val < N - t := Nat.lt_of_not_ge hiOld
        have hile : i.val ≤ N - (t + 1) := by omega
        exact le_antisymm hile hi)
      subst i
      have hd_eq_c : d = c := Fin.ext (by
        dsimp [d, start, c]
        omega)
      unfold smetSwitchColumn
      rw [hd_eq_c]
      simp [switchReach.start, hstartLast]
