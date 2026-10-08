-- Prove2me | solution 1 for ProofsInTheBook.Chapter33.latin_rectangle_complete
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:08:59.066196+00:00
-- url     : https://prove2.me/submissions/99a33cdd-8577-4217-ae5e-4d353acc6cb4

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

theorem solution {r n : ℕ} (R : Fin r → Fin n → Fin n)
    (hrow : ∀ i : Fin r, Function.Injective (R i))
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j)
    (hrn : r ≤ n) :
    ∃ L : Fin n → Fin n → Fin n,
      IsLatinSquare L ∧ ∀ i : Fin r, ∀ j,
        L (Fin.castLE hrn i) j = R i j := by
  classical
  let motive : ℕ → Prop := fun d =>
    ∀ r : ℕ, ∀ R : Fin r → Fin n → Fin n,
      (∀ i : Fin r, Function.Injective (R i)) →
      (∀ j : Fin n, Function.Injective fun i : Fin r => R i j) →
      ∀ hrn : r ≤ n, d = n - r →
        ∃ L : Fin n → Fin n → Fin n,
          IsLatinSquare L ∧ ∀ i : Fin r, ∀ j,
            L (Fin.castLE hrn i) j = R i j
  have step : ∀ d, (∀ e < d, motive e) → motive d := by
    intro d ih r R hrow hcol hrn hd
    by_cases hr_eq : r = n
    · subst r
      let L : Fin n → Fin n → Fin n := fun i j => R (Fin.cast rfl i) j
      refine ⟨L, ?_, ?_⟩
      · constructor
        · intro i
          simpa [L] using hrow (Fin.cast rfl i)
        · intro j i₁ i₂ h
          have h' : (Fin.cast rfl i₁ : Fin n) = Fin.cast rfl i₂ := hcol j h
          simpa using h'
      · intro i j
        simp [L]
    · have hlt : r < n := lt_of_le_of_ne hrn hr_eq
      obtain ⟨nextRow, hnextRow, havoid⟩ :=
        latin_rectangle_extend_one R hrow hcol hlt
      let Rplus : Fin (r + 1) → Fin n → Fin n :=
        fun i j => if hi : i.val < r then R ⟨i.val, hi⟩ j else nextRow j
      have hrowPlus : ∀ i : Fin (r + 1), Function.Injective (Rplus i) := by
        intro i j₁ j₂ h
        by_cases hi : i.val < r
        · have h' : R ⟨i.val, hi⟩ j₁ = R ⟨i.val, hi⟩ j₂ := by
            simpa [Rplus, hi] using h
          exact hrow ⟨i.val, hi⟩ h'
        · have h' : nextRow j₁ = nextRow j₂ := by
            simpa [Rplus, hi] using h
          exact hnextRow h'
      have hcolPlus : ∀ j : Fin n, Function.Injective fun i : Fin (r + 1) => Rplus i j := by
        intro j i₁ i₂ h
        by_cases h₁ : i₁.val < r
        · by_cases h₂ : i₂.val < r
          · have hR : R ⟨i₁.val, h₁⟩ j = R ⟨i₂.val, h₂⟩ j := by
              simpa [Rplus, h₁, h₂] using h
            have hii : (⟨i₁.val, h₁⟩ : Fin r) = ⟨i₂.val, h₂⟩ := hcol j hR
            exact Fin.ext (by simpa using congrArg Fin.val hii)
          · have hbad : R ⟨i₁.val, h₁⟩ j = nextRow j := by
              simpa [Rplus, h₁, h₂] using h
            exact False.elim (havoid ⟨i₁.val, h₁⟩ j hbad.symm)
        · by_cases h₂ : i₂.val < r
          · have hbad : nextRow j = R ⟨i₂.val, h₂⟩ j := by
              simpa [Rplus, h₁, h₂] using h
            exact False.elim (havoid ⟨i₂.val, h₂⟩ j hbad)
          · exact Fin.ext (by omega)
      have hrplus : r + 1 ≤ n := by omega
      have hdec : n - (r + 1) < d := by omega
      obtain ⟨L, hLatin, hExt⟩ :=
        ih (n - (r + 1)) hdec (r + 1) Rplus hrowPlus hcolPlus hrplus rfl
      refine ⟨L, hLatin, ?_⟩
      intro i j
      let iPlus : Fin (r + 1) := Fin.castLE (Nat.le_succ r) i
      have hrowpos : Fin.castLE hrn i = Fin.castLE hrplus iPlus := by
        exact Fin.ext (by simp [iPlus, Fin.castLE])
      have hRplus : Rplus iPlus j = R i j := by
        have hi : iPlus.val < r := by
          dsimp [iPlus]
          exact i.isLt
        simp [Rplus, iPlus]
      rw [hrowpos, hExt iPlus j, hRplus]
  exact (Nat.strong_induction_on (p := motive) (n - r) step) r R hrow hcol hrn rfl
