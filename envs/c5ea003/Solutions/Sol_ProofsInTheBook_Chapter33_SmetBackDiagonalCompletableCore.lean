-- Prove2me | solution 1 for ProofsInTheBook.Chapter33.SmetBackDiagonalCompletableCore
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:08:34.789038+00:00
-- url     : https://prove2.me/submissions/ae4d336a-4b21-4e86-9d15-76cb5d35ff0d

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

theorem hall_system_of_distinct_representatives {ι α : Type*} [DecidableEq α]
    (available : ι → Finset α)
    (hHall : ∀ rows : Finset ι, rows.card ≤ (rows.biUnion available).card) :
    ∃ choice : ι → α, Function.Injective choice ∧ ∀ row, choice row ∈ available row :=
  (Finset.all_card_le_biUnion_card_iff_exists_injective available).mp hHall

/--
A regular finite family satisfies Hall's condition.

If every set in the family has size `d`, and each element belongs to at most
`d` sets, then every subfamily has union at least as large as its index set.
This is the double-counting form used for Latin rectangle extension.
-/
lemma hall_condition_of_regular_family {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (A : ι → Finset α) (d : ℕ)
    (hcard : ∀ i, (A i).card = d)
    (hfiber : ∀ a, ((Finset.univ : Finset ι).filter fun i => a ∈ A i).card ≤ d)
    (hd : 0 < d) :
    ∀ S : Finset ι, S.card ≤ (S.biUnion A).card := by
  intro S
  let T := S.biUnion A
  let I : Finset (ι × α) := (S ×ˢ T).filter fun p => p.2 ∈ A p.1
  have hI_le : I.card ≤ T.card * d := by
    have hmap : (I : Set (ι × α)).MapsTo Prod.snd T := by
      intro p hp
      have hp' : p ∈ I := hp
      have hmem : p ∈ S ×ˢ T ∧ p.2 ∈ A p.1 := by
        simpa [I] using (Finset.mem_filter.mp hp')
      exact (Finset.mem_product.mp hmem.1).2
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      (∑ b ∈ T, #{p ∈ I | Prod.snd p = b}) ≤ ∑ b ∈ T, d := by
        apply Finset.sum_le_sum
        intro b _hb
        have hle_to_global : #{p ∈ I | Prod.snd p = b} ≤
            ((Finset.univ : Finset ι).filter fun i => b ∈ A i).card := by
          refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
          · intro p hp
            have hpI : p ∈ I := (Finset.mem_filter.mp hp).1
            have hpb : Prod.snd p = b := (Finset.mem_filter.mp hp).2
            have hmem : p ∈ S ×ˢ T ∧ p.2 ∈ A p.1 := by
              simpa [I] using (Finset.mem_filter.mp hpI)
            have hbA : b ∈ A p.1 := by
              simpa [Prod.snd, hpb.symm] using hmem.2
            simp [hbA]
          · intro p hp q hq hpq
            have hpb : Prod.snd p = b := (Finset.mem_filter.mp hp).2
            have hqb : Prod.snd q = b := (Finset.mem_filter.mp hq).2
            exact Prod.ext hpq (by simp [hpb, hqb])
        exact le_trans hle_to_global (hfiber b)
      _ = T.card * d := by simp [Nat.mul_comm]
  have hI_eq : I.card = S.card * d := by
    have hmap : (I : Set (ι × α)).MapsTo Prod.fst S := by
      intro p hp
      have hp' : p ∈ I := hp
      have hmem : p ∈ S ×ˢ T ∧ p.2 ∈ A p.1 := by
        simpa [I] using (Finset.mem_filter.mp hp')
      exact (Finset.mem_product.mp hmem.1).1
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      (∑ i ∈ S, #{p ∈ I | Prod.fst p = i}) = ∑ i ∈ S, d := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfib_eq : #{p ∈ I | Prod.fst p = i} = (A i).card := by
          have hle1 : #{p ∈ I | Prod.fst p = i} ≤ (A i).card := by
            refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
            · intro p hp
              have hpI : p ∈ I := (Finset.mem_filter.mp hp).1
              have hmem : p ∈ S ×ˢ T ∧ p.2 ∈ A p.1 := by
                simpa [I] using (Finset.mem_filter.mp hpI)
              have hpi : Prod.fst p = i := (Finset.mem_filter.mp hp).2
              simpa [Prod.fst, hpi] using hmem.2
            · intro p hp q hq hpq
              have hpi : Prod.fst p = i := (Finset.mem_filter.mp hp).2
              have hqi : Prod.fst q = i := (Finset.mem_filter.mp hq).2
              exact Prod.ext (by simp [hpi, hqi]) hpq
          have hle2 : (A i).card ≤ #{p ∈ I | Prod.fst p = i} := by
            refine Finset.card_le_card_of_injOn (fun a => (i, a)) ?_ ?_
            · intro a ha
              have haT : a ∈ T := Finset.mem_biUnion.mpr ⟨i, hi, ha⟩
              have hpI : (i, a) ∈ I := by
                exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, haT⟩, ha⟩
              exact Finset.mem_filter.mpr ⟨hpI, rfl⟩
            · intro a _ b _ hab
              exact Prod.mk.inj hab |>.2
          exact le_antisymm hle1 hle2
        simpa [hcard i] using hfib_eq
      _ = S.card * d := by simp [Nat.mul_comm]
  have hmul : S.card * d ≤ T.card * d := by simpa [hI_eq] using hI_le
  exact Nat.le_of_mul_le_mul_right hmul hd

/-!
### Latin rectangles

The first Hall application in the book says that every `r × n` Latin
rectangle with `r < n` can be extended by one more row.
-/



lemma rectangleAvailable_card {r n : ℕ} {R : Fin r → Fin n → Fin n}
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j) (j : Fin n) :
    (rectangleAvailable R j).card = n - r := by
  classical
  let used : Finset (Fin n) := (Finset.univ : Finset (Fin r)).image fun i => R i j
  have hused_card : used.card = r := by
    dsimp [used]
    rw [Finset.card_image_of_injective]
    · simp
    · exact hcol j
  have hAvail : rectangleAvailable R j = (Finset.univ : Finset (Fin n)) \ used := by
    ext a
    simp [rectangleAvailable, used]
  rw [hAvail]
  have hsub : used ⊆ (Finset.univ : Finset (Fin n)) := by
    intro a _ha
    simp
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin, hused_card]



lemma symbolColumn_spec {r n : ℕ} {R : Fin r → Fin n → Fin n}
    (hrow : ∀ i : Fin r, Function.Injective (R i)) (a : Fin n) (i : Fin r) :
    R i (symbolColumn hrow a i) = a :=
  Classical.choose_spec ((hrow i).surjective_of_finite (Equiv.refl (Fin n)) a)

lemma symbolColumn_injective {r n : ℕ} {R : Fin r → Fin n → Fin n}
    (hrow : ∀ i : Fin r, Function.Injective (R i))
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j) (a : Fin n) :
    Function.Injective (symbolColumn hrow a) := by
  intro i k hik
  have hi : R i (symbolColumn hrow a i) = a := symbolColumn_spec hrow a i
  have hk : R k (symbolColumn hrow a k) = a := symbolColumn_spec hrow a k
  have hsame : R i (symbolColumn hrow a i) = R k (symbolColumn hrow a i) := by
    rw [hi]
    rw [hik]
    exact hk.symm
  exact hcol (symbolColumn hrow a i) hsame

lemma rectangleAvailable_fiber_card {r n : ℕ} {R : Fin r → Fin n → Fin n}
    (hrow : ∀ i : Fin r, Function.Injective (R i))
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j) (a : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter fun j => a ∈ rectangleAvailable R j).card =
      n - r := by
  classical
  let usedCols : Finset (Fin n) :=
    (Finset.univ : Finset (Fin r)).image (symbolColumn hrow a)
  have hused_card : usedCols.card = r := by
    dsimp [usedCols]
    rw [Finset.card_image_of_injective]
    · simp
    · exact symbolColumn_injective hrow hcol a
  have hfilter :
      ((Finset.univ : Finset (Fin n)).filter fun j => a ∈ rectangleAvailable R j) =
        (Finset.univ : Finset (Fin n)) \ usedCols := by
    ext j
    simp [rectangleAvailable, usedCols]
    constructor
    · intro h i hji
      have hspec := symbolColumn_spec hrow a i
      exact h i (by rw [← hji]; exact hspec)
    · intro h i hij
      have hspec := symbolColumn_spec hrow a i
      have hji : j = symbolColumn hrow a i := hrow i (by rw [hij, hspec])
      exact h i hji.symm
  rw [hfilter]
  have hsub : usedCols ⊆ (Finset.univ : Finset (Fin n)) := by
    intro j _hj
    simp
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin, hused_card]

/--
Book Lemma 1: an `r × n` Latin rectangle with `r < n` can be extended by one
row.  The returned row is a permutation of the symbols and avoids every symbol
already present in its column.
-/
theorem latin_rectangle_extend_one {r n : ℕ} (R : Fin r → Fin n → Fin n)
    (hrow : ∀ i : Fin r, Function.Injective (R i))
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j)
    (hrn : r < n) :
    ∃ row : Fin n → Fin n, Function.Injective row ∧ ∀ i j, row j ≠ R i j := by
  classical
  have hd : 0 < n - r := Nat.sub_pos_of_lt hrn
  have hHall : ∀ S : Finset (Fin n), S.card ≤ (S.biUnion (rectangleAvailable R)).card :=
    hall_condition_of_regular_family (A := rectangleAvailable R) (d := n - r)
      (fun j => rectangleAvailable_card hcol j)
      (fun a => le_of_eq (rectangleAvailable_fiber_card hrow hcol a)) hd
  obtain ⟨row, hrow_inj, hrow_mem⟩ :=
    hall_system_of_distinct_representatives (rectangleAvailable R) hHall
  refine ⟨row, hrow_inj, ?_⟩
  intro i j
  have h := hrow_mem j
  simp [rectangleAvailable] at h
  exact fun hEq => h i hEq.symm

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



lemma smetBackPartial_back_diagonal {N : ℕ} (L₀ : Fin N → Fin N → Fin N)
    {i j : Fin (N + 1)} (hdiag : i.val + j.val = N) :
    smetBackPartial L₀ i j = some (Fin.last N) := by
  simp [smetBackPartial, hdiag]











































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



@[simp] lemma smetRectInitial_old {N : ℕ}
    (L₀ : Fin N → Fin N → Fin N) (i : Fin N) (j : Fin (N + 1))
    (hj : j.val < N) :
    smetRectInitial L₀ i j =
      Fin.castSucc (L₀ i ⟨j.val, hj⟩) := by
  simp [smetRectInitial, hj]

@[simp] lemma smetRectInitial_last {N : ℕ}
    (L₀ : Fin N → Fin N → Fin N) (i : Fin N) :
    smetRectInitial L₀ i (Fin.last N) = Fin.last N := by
  simp [smetRectInitial, Fin.last]





lemma smetRectInitial_row_injective {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀) :
    ∀ i : Fin N, Function.Injective (smetRectInitial L₀ i) := by
  intro i j₁ j₂ h
  unfold smetRectInitial at h
  by_cases h₁ : j₁.val < N
  · by_cases h₂ : j₂.val < N
    · simp [h₁, h₂] at h
      have hcols :
          (⟨j₁.val, h₁⟩ : Fin N) = ⟨j₂.val, h₂⟩ :=
        hL₀.1 i h
      exact Fin.ext (by simpa using congrArg Fin.val hcols)
    · simp [h₁, h₂] at h
  · by_cases h₂ : j₂.val < N
    · simp [h₁, h₂] at h
      exact False.elim (fin_castSucc_ne_last _ h.symm)
    · have hj₁ : j₁ = Fin.last N := Fin.ext (by
        have hj₁le : j₁.val ≤ N := Nat.lt_succ_iff.mp j₁.isLt
        have hj₁ge : N ≤ j₁.val := Nat.le_of_not_gt h₁
        simpa [Fin.last] using le_antisymm hj₁le hj₁ge)
      have hj₂ : j₂ = Fin.last N := Fin.ext (by
        have hj₂le : j₂.val ≤ N := Nat.lt_succ_iff.mp j₂.isLt
        have hj₂ge : N ≤ j₂.val := Nat.le_of_not_gt h₂
        simpa [Fin.last] using le_antisymm hj₂le hj₂ge)
      exact hj₁.trans hj₂.symm

lemma smetRectInitial_col_injective {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀)
    (j : Fin (N + 1)) (hj : j.val < N) :
    Function.Injective fun i : Fin N => smetRectInitial L₀ i j := by
  intro i₁ i₂ h
  simp [smetRectInitial, hj] at h
  exact hL₀.2 ⟨j.val, hj⟩ h



lemma smetRectInitial_invariant {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀)
    (hN : 0 < N) :
    SmetRectStageInvariant L₀ 0 (smetRectInitial L₀) := by
  constructor
  · exact smetRectInitial_row_injective hL₀
  · exact smetRectInitial_col_injective hL₀
  · intro i₁ _i₂ hi₁ _hi₂ _h
    have : i₁.val < N := i₁.isLt
    omega
  · intro i _hi
    exact smetRectInitial_last L₀ i
  · intro i j _htj hj
    exact smetRectInitial_old L₀ i j hj
  · intro i j hj _hij
    exact smetRectInitial_old L₀ i j hj
  · intro i hi
    have : i.val < N := i.isLt
    omega

lemma smetRectStep_invariant {N t : ℕ}
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

lemma smetRectStage_invariant {N t : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀)
    (ht : t < N) :
    SmetRectStageInvariant L₀ t (smetRectStage L₀ t) := by
  induction t with
  | zero =>
      exact smetRectInitial_invariant hL₀ (by omega)
  | succ t ih =>
      change SmetRectStageInvariant L₀ (t + 1)
        (smetRectStep (smetRectStage L₀ t) t)
      exact smetRectStep_invariant ht (ih (by omega))





















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

theorem solution {N : ℕ} (hN : 3 ≤ N)
    (L₀ : Fin N → Fin N → Fin N) (hL₀ : IsLatinSquare L₀) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetBackPartial L₀) L := by
  let R : Fin N → Fin (N + 1) → Fin (N + 1) :=
    smetRectStage L₀ (N - 1)
  have hInv : SmetRectStageInvariant L₀ (N - 1) R := by
    dsimp [R]
    exact smetRectStage_invariant hL₀ (by omega)
  have hlast_ne_of_pos :
      ∀ i : Fin N, 0 < i.val → R i (Fin.last N) ≠ Fin.last N := by
    intro i hiPos hlast
    let d : Fin (N + 1) := ⟨N - i.val, by omega⟩
    have hactive : N - (N - 1) ≤ i.val := by omega
    have hdiag : R i d = Fin.last N := by
      simpa [d] using hInv.diag_active i hactive
    have hd_eq_last : d = Fin.last N := hInv.row_inj i (by rw [hdiag, hlast])
    have hv : N - i.val = N := by
      simpa [d, Fin.last] using congrArg Fin.val hd_eq_last
    omega
  have hlast_col_inj :
      Function.Injective fun i : Fin N => R i (Fin.last N) := by
    intro i₁ i₂ h
    by_cases h₁zero : i₁.val = 0
    · by_cases h₂zero : i₂.val = 0
      · exact Fin.ext (h₁zero.trans h₂zero.symm)
      · have h₁last : R i₁ (Fin.last N) = Fin.last N := by
          exact hInv.last_unactive_new i₁ (by omega)
        have h₂pos : 0 < i₂.val := by omega
        have h₂last : R i₂ (Fin.last N) = Fin.last N := by
          exact h.symm.trans h₁last
        exact False.elim (hlast_ne_of_pos i₂ h₂pos h₂last)
    · have h₁pos : 0 < i₁.val := by omega
      by_cases h₂zero : i₂.val = 0
      · have h₂last : R i₂ (Fin.last N) = Fin.last N := by
          exact hInv.last_unactive_new i₂ (by omega)
        have h₁last : R i₁ (Fin.last N) = Fin.last N := by
          exact h.trans h₂last
        exact False.elim (hlast_ne_of_pos i₁ h₁pos h₁last)
      · have h₂pos : 0 < i₂.val := by omega
        exact hInv.last_active_inj i₁ i₂ (by omega) (by omega) h
  have hcolR : ∀ j : Fin (N + 1), Function.Injective fun i : Fin N => R i j := by
    intro j
    by_cases hj : j.val < N
    · exact hInv.col_inj j hj
    · have hjlast : j = Fin.last N := Fin.ext (by
        have hjle : j.val ≤ N := Nat.lt_succ_iff.mp j.isLt
        have hjge : N ≤ j.val := Nat.le_of_not_gt hj
        simpa [Fin.last] using le_antisymm hjle hjge)
      subst j
      exact hlast_col_inj
  obtain ⟨lastRow, hlastRow_inj, hlastRow_avoid⟩ :
      ∃ row : Fin (N + 1) → Fin (N + 1), Function.Injective row ∧
        ∀ i j, row j ≠ R i j :=
    latin_rectangle_extend_one R hInv.row_inj hcolR (by omega)
  let L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) :=
    fun i j => if hi : i.val < N then R ⟨i.val, hi⟩ j else lastRow j
  have hrowL : ∀ i : Fin (N + 1), Function.Injective (L i) := by
    intro i j₁ j₂ h
    by_cases hi : i.val < N
    · have h' : R ⟨i.val, hi⟩ j₁ = R ⟨i.val, hi⟩ j₂ := by
        simpa [L, hi] using h
      exact hInv.row_inj ⟨i.val, hi⟩ h'
    · have h' : lastRow j₁ = lastRow j₂ := by
        simpa [L, hi] using h
      exact hlastRow_inj h'
  have hcolL : ∀ j : Fin (N + 1), Function.Injective fun i : Fin (N + 1) => L i j := by
    intro j i₁ i₂ h
    by_cases h₁ : i₁.val < N
    · by_cases h₂ : i₂.val < N
      · have hR : R ⟨i₁.val, h₁⟩ j = R ⟨i₂.val, h₂⟩ j := by
          simpa [L, h₁, h₂] using h
        have hii : (⟨i₁.val, h₁⟩ : Fin N) = ⟨i₂.val, h₂⟩ :=
          hcolR j hR
        exact Fin.ext (by simpa using congrArg Fin.val hii)
      · have hlast : i₂ = Fin.last N := Fin.ext (by
          have hle : i₂.val ≤ N := Nat.lt_succ_iff.mp i₂.isLt
          have hge : N ≤ i₂.val := Nat.le_of_not_gt h₂
          simpa [Fin.last] using le_antisymm hle hge)
        subst i₂
        have hbad : lastRow j = R ⟨i₁.val, h₁⟩ j := by
          simpa [L, h₁] using h.symm
        exact False.elim (hlastRow_avoid ⟨i₁.val, h₁⟩ j hbad)
    · by_cases h₂ : i₂.val < N
      · have hlast : i₁ = Fin.last N := Fin.ext (by
          have hle : i₁.val ≤ N := Nat.lt_succ_iff.mp i₁.isLt
          have hge : N ≤ i₁.val := Nat.le_of_not_gt h₁
          simpa [Fin.last] using le_antisymm hle hge)
        subst i₁
        have hbad : lastRow j = R ⟨i₂.val, h₂⟩ j := by
          simpa [L, h₂] using h
        exact False.elim (hlastRow_avoid ⟨i₂.val, h₂⟩ j hbad)
      · have hi₁last : i₁ = Fin.last N := Fin.ext (by
          have hle : i₁.val ≤ N := Nat.lt_succ_iff.mp i₁.isLt
          have hge : N ≤ i₁.val := Nat.le_of_not_gt h₁
          simpa [Fin.last] using le_antisymm hle hge)
        have hi₂last : i₂ = Fin.last N := Fin.ext (by
          have hle : i₂.val ≤ N := Nat.lt_succ_iff.mp i₂.isLt
          have hge : N ≤ i₂.val := Nat.le_of_not_gt h₂
          simpa [Fin.last] using le_antisymm hle hge)
        exact hi₁last.trans hi₂last.symm
  have hlastRow_zero : lastRow 0 = Fin.last N := by
    by_contra hne
    have hvlt : (lastRow 0).val < N := by
      have hvle : (lastRow 0).val ≤ N := Nat.lt_succ_iff.mp (lastRow 0).isLt
      have hvne : (lastRow 0).val ≠ N := by
        intro hv
        exact hne (Fin.ext (by simpa [Fin.last] using hv))
      omega
    let a : Fin N := ⟨(lastRow 0).val, hvlt⟩
    let zN : Fin N := ⟨0, by omega⟩
    obtain ⟨i₀, hi₀⟩ :=
      (hL₀.2 zN).surjective_of_finite (Equiv.refl (Fin N)) a
    have hzero_lt : (0 : Fin (N + 1)).val < N := by
      show 0 < N
      omega
    have hR0 : R i₀ 0 = Fin.castSucc (L₀ i₀ zN) := by
      have hreq := hInv.required_old i₀ (0 : Fin (N + 1)) hzero_lt (by simpa using i₀.isLt)
      simpa [zN] using hreq
    have hcasta : Fin.castSucc a = lastRow 0 := Fin.ext (by rfl)
    have hRlast : R i₀ 0 = lastRow 0 := by
      calc
        R i₀ 0 = Fin.castSucc (L₀ i₀ zN) := hR0
        _ = Fin.castSucc a := congrArg Fin.castSucc hi₀
        _ = lastRow 0 := hcasta
    exact hlastRow_avoid i₀ 0 hRlast.symm
  refine ⟨L, ?_⟩
  constructor
  · exact ⟨hrowL, hcolL⟩
  · intro i j a hcell
    by_cases hi : i.val < N
    · let ii : Fin N := ⟨i.val, hi⟩
      by_cases hdiag : i.val + j.val = N
      · have ha : a = Fin.last N := by
          simpa [smetBackPartial, hdiag] using hcell.symm
        subst a
        have hj_eq : j = ⟨N - ii.val, by omega⟩ := Fin.ext (by
          dsimp [ii]
          omega)
        have hdiagR : R ii ⟨N - ii.val, by omega⟩ = Fin.last N := by
          by_cases hrow0 : ii.val = 0
          · have hdlast : (⟨N - ii.val, by omega⟩ : Fin (N + 1)) = Fin.last N :=
              Fin.ext (by
                have hv : N - ii.val = N := by omega
                simpa [Fin.last] using hv)
            rw [hdlast]
            exact hInv.last_unactive_new ii (by omega)
          · have hactive : N - (N - 1) ≤ ii.val := by omega
            exact hInv.diag_active ii hactive
        simpa [L, hi, R, ii, hj_eq] using hdiagR
      · by_cases hlt : i.val + j.val < N
        · have hjN : j.val < N := by omega
          have ha : a = Fin.castSucc (L₀ ii ⟨j.val, hjN⟩) := by
            simpa [smetBackPartial, hdiag, hlt, ii] using hcell.symm
          subst a
          have hreq := hInv.required_old ii j hjN (by simpa [ii] using hlt)
          simpa [L, hi, R] using hreq
        · simp [smetBackPartial, hdiag, hlt] at hcell
    · have hilast : i = Fin.last N := Fin.ext (by
        have hle : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
        have hge : N ≤ i.val := Nat.le_of_not_gt hi
        simpa [Fin.last] using le_antisymm hle hge)
      subst i
      have hlastInfo : j = 0 ∧ a = Fin.last N := by
        by_cases hdiag : (Fin.last N).val + j.val = N
        · have hj0 : j = 0 := Fin.ext (by
            simpa [Fin.last] using hdiag)
          have ha : a = Fin.last N := by
            have htmp :
                smetBackPartial L₀ (Fin.last N) j = some (Fin.last N) :=
              smetBackPartial_back_diagonal L₀ hdiag
            have hsome : some (Fin.last N) = some a := by
              simpa [htmp] using hcell
            exact (Option.some.inj hsome).symm
          exact ⟨hj0, ha⟩
        · have hlt : ¬ (Fin.last N).val + j.val < N := by
            intro hlt'
            have hv : (Fin.last N).val = N := by simp [Fin.last]
            omega
          simp [smetBackPartial, hdiag, hlt] at hcell
          exact ⟨hcell.1, hcell.2.symm⟩
      rcases hlastInfo with ⟨hj0, ha⟩
      rw [hj0, ha]
      simpa [L, hlastRow_zero]
