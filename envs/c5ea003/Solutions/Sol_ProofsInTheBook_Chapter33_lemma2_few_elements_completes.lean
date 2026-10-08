-- Prove2me | solution 1 for ProofsInTheBook.Chapter33.lemma2_few_elements_completes
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:09:02.750796+00:00
-- url     : https://prove2.me/submissions/a90964d7-fbed-40b3-bb1f-b399a7ee5de3

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







lemma nat_ineq (n k : ℕ) (hkpos : 0 < k) (hkn : k ≤ n) : n ≤ (n - k + 1) * k := by
  have hz : (n : ℤ) ≤ ((n : ℤ) - (k : ℤ) + 1) * (k : ℤ) := by nlinarith
  exact_mod_cast hz



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

lemma isPartialLatin_relabelPartial {n : ℕ}
    (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P) :
    IsPartialLatin (relabelPartial rowPerm colPerm symPerm P) := by
  constructor
  · intro i j₁ j₂ a h₁ h₂
    have h₁P : P (rowPerm i) (colPerm j₁) = some (symPerm.symm a) :=
      (relabelPartial_eq_some_iff rowPerm colPerm symPerm P i j₁ a).mp h₁
    have h₂P : P (rowPerm i) (colPerm j₂) = some (symPerm.symm a) :=
      (relabelPartial_eq_some_iff rowPerm colPerm symPerm P i j₂ a).mp h₂
    have hcol : colPerm j₁ = colPerm j₂ :=
      hP.1 (rowPerm i) (colPerm j₁) (colPerm j₂) (symPerm.symm a) h₁P h₂P
    exact colPerm.injective hcol
  · intro i₁ i₂ j a h₁ h₂
    have h₁P : P (rowPerm i₁) (colPerm j) = some (symPerm.symm a) :=
      (relabelPartial_eq_some_iff rowPerm colPerm symPerm P i₁ j a).mp h₁
    have h₂P : P (rowPerm i₂) (colPerm j) = some (symPerm.symm a) :=
      (relabelPartial_eq_some_iff rowPerm colPerm symPerm P i₂ j a).mp h₂
    have hrow : rowPerm i₁ = rowPerm i₂ :=
      hP.2 (rowPerm i₁) (rowPerm i₂) (colPerm j) (symPerm.symm a) h₁P h₂P
    exact rowPerm.injective hrow

lemma isLatinSquare_relabelSquare {n : ℕ}
    (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) :
    IsLatinSquare (relabelSquare rowPerm colPerm symPerm L) := by
  constructor
  · intro i j₁ j₂ h
    have h' : L (rowPerm i) (colPerm j₁) = L (rowPerm i) (colPerm j₂) :=
      symPerm.injective h
    have hcol : colPerm j₁ = colPerm j₂ := hL.1 (rowPerm i) h'
    exact colPerm.injective hcol
  · intro j i₁ i₂ h
    have h' : L (rowPerm i₁) (colPerm j) = L (rowPerm i₂) (colPerm j) :=
      symPerm.injective h
    have hrow : rowPerm i₁ = rowPerm i₂ := hL.2 (colPerm j) h'
    exact rowPerm.injective hrow

lemma completes_relabelPartial {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    {P : Fin n → Fin n → Option (Fin n)} {L : Fin n → Fin n → Fin n}
    (hL : Completes P L) :
    Completes (relabelPartial rowPerm colPerm symPerm P)
      (relabelSquare rowPerm colPerm symPerm L) := by
  constructor
  · exact isLatinSquare_relabelSquare rowPerm colPerm symPerm hL.1
  · intro i j a hcell
    have hP : P (rowPerm i) (colPerm j) = some (symPerm.symm a) :=
      (relabelPartial_eq_some_iff rowPerm colPerm symPerm P i j a).mp hcell
    have hbase := hL.2 (rowPerm i) (colPerm j) (symPerm.symm a) hP
    simp [relabelSquare, hbase]

lemma completes_of_relabelPartial {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    {P : Fin n → Fin n → Option (Fin n)} {L' : Fin n → Fin n → Fin n}
    (hL' : Completes (relabelPartial rowPerm colPerm symPerm P) L') :
    Completes P (relabelSquare rowPerm.symm colPerm.symm symPerm.symm L') := by
  constructor
  · exact isLatinSquare_relabelSquare rowPerm.symm colPerm.symm symPerm.symm hL'.1
  · intro i j a hP
    have hcell :
        relabelPartial rowPerm colPerm symPerm P (rowPerm.symm i) (colPerm.symm j) =
          some (symPerm a) := by
      simp [relabelPartial, hP]
    have hbase := hL'.2 (rowPerm.symm i) (colPerm.symm j) (symPerm a) hcell
    simp [relabelSquare, hbase]

lemma completion_exists_relabelPartial_iff {n : ℕ}
    (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) :
    (∃ L : Fin n → Fin n → Fin n, Completes (relabelPartial rowPerm colPerm symPerm P) L) ↔
      ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  constructor
  · intro h
    rcases h with ⟨L', hL'⟩
    exact ⟨relabelSquare rowPerm.symm colPerm.symm symPerm.symm L',
      completes_of_relabelPartial rowPerm colPerm symPerm hL'⟩
  · intro h
    rcases h with ⟨L, hL⟩
    exact ⟨relabelSquare rowPerm colPerm symPerm L,
      completes_relabelPartial rowPerm colPerm symPerm hL⟩

lemma filledCells_relabelPartial {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) :
    filledCells (relabelPartial rowPerm colPerm symPerm P) =
      (filledCells P).image (fun ij : Fin n × Fin n =>
        (rowPerm.symm ij.1, colPerm.symm ij.2)) := by
  classical
  ext ij
  constructor
  · intro hij
    have hfilled : (P (rowPerm ij.1) (colPerm ij.2)).isSome := by
      simpa [filledCells, relabelPartial] using hij
    refine Finset.mem_image.mpr ⟨(rowPerm ij.1, colPerm ij.2), ?_, ?_⟩
    · simpa [filledCells] using hfilled
    · simp
  · intro hij
    rcases Finset.mem_image.mp hij with ⟨ijOld, hOld, hijEq⟩
    have hfilledOld : (P ijOld.1 ijOld.2).isSome := by
      simpa [filledCells] using hOld
    have hi : ij.1 = rowPerm.symm ijOld.1 := (congrArg Prod.fst hijEq).symm
    have hj : ij.2 = colPerm.symm ijOld.2 := (congrArg Prod.snd hijEq).symm
    simp [filledCells, relabelPartial, hi, hj, hfilledOld]

lemma filledCells_relabelPartial_card {n : ℕ}
    (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) :
    (filledCells (relabelPartial rowPerm colPerm symPerm P)).card =
      (filledCells P).card := by
  rw [filledCells_relabelPartial rowPerm colPerm symPerm P]
  rw [Finset.card_image_of_injective]
  intro x y h
  exact Prod.ext (rowPerm.symm.injective (congrArg Prod.fst h))
    (colPerm.symm.injective (congrArg Prod.snd h))

























































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













lemma cellValue_spec_of_isSome {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    {ij : Fin n × Fin n} (hfilled : (P ij.1 ij.2).isSome) :
    P ij.1 ij.2 = some (cellValue P ij) := by
  classical
  unfold cellValue
  by_cases h : ∃ a, P ij.1 ij.2 = some a
  · simpa [h] using (Classical.choose_spec h)
  · cases hcell : P ij.1 ij.2 with
    | none =>
        simp [hcell] at hfilled
    | some a =>
        exact False.elim (h ⟨a, hcell⟩)

lemma mem_elementsUsed_of_cell {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    {i j a : Fin n} (hcell : P i j = some a) : a ∈ elementsUsed P := by
  exact by
    simp [elementsUsed]
    exact ⟨i, j, hcell⟩

lemma mem_rowsUsed_of_cell {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    {i j a : Fin n} (hcell : P i j = some a) : i ∈ rowsUsed P := by
  exact by
    simp [rowsUsed]
    exact ⟨j, a, hcell⟩

lemma rowFilledCols_card_eq_rowFill {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    (rowFilledCols P i).card = rowFill P i := by
  classical
  rw [rowFill, rowFilledCols, rowCells]
  refine Finset.card_bij (fun j _ => (i, j)) ?hmem ?hinj ?hsurj
  · intro j hj
    simpa [filledCells] using hj
  · intro j₁ _ j₂ _ h
    exact congrArg Prod.snd h
  · intro ij hij
    have hi : ij.1 = i := (Finset.mem_filter.mp hij).2
    refine ⟨ij.2, ?_, ?_⟩
    · have hfilled : (P ij.1 ij.2).isSome := by
        simpa [filledCells] using (Finset.mem_filter.mp hij).1
      simpa [rowFilledCols, hi] using hfilled
    · exact Prod.ext hi.symm rfl

lemma rowFill_pos_iff_mem_rowsUsed {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    0 < rowFill P i ↔ i ∈ rowsUsed P := by
  classical
  rw [← rowFilledCols_card_eq_rowFill]
  constructor
  · intro hpos
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    have hsome : (P i j).isSome := by simpa [rowFilledCols] using hj
    cases hcell : P i j with
    | none =>
        simp [hcell] at hsome
    | some a =>
        exact mem_rowsUsed_of_cell hcell
  · intro hrow
    rcases (by simpa [rowsUsed] using hrow) with ⟨j, a, hcell⟩
    exact Finset.card_pos.mpr ⟨j, by simp [rowFilledCols, hcell]⟩

lemma rowFill_eq_zero_iff_row_empty {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    rowFill P i = 0 ↔ ∀ j, P i j = none := by
  classical
  constructor
  · intro hzero j
    cases hcell : P i j with
    | none => rfl
    | some a =>
        have hpos : 0 < rowFill P i :=
          (rowFill_pos_iff_mem_rowsUsed P i).2 (mem_rowsUsed_of_cell hcell)
        omega
  · intro hempty
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hrow : i ∈ rowsUsed P := (rowFill_pos_iff_mem_rowsUsed P i).1 hpos
    rcases (by simpa [rowsUsed] using hrow) with ⟨j, a, hcell⟩
    rw [hempty j] at hcell
    cases hcell

lemma rowSymbols_card_eq_rowFill {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P) (i : Fin n) :
    (rowSymbols P i).card = rowFill P i := by
  classical
  rw [← rowFilledCols_card_eq_rowFill]
  symm
  refine Finset.card_bij
    (fun j _ => cellValue P (i, j)) ?hmem ?hinj ?hsurj
  · intro j hj
    have hsome : (P i j).isSome := by simpa [rowFilledCols] using hj
    have hcell : P i j = some (cellValue P (i, j)) :=
      cellValue_spec_of_isSome (P := P) (ij := (i, j)) hsome
    simp [rowSymbols]
    exact ⟨j, hcell⟩
  · intro j₁ hj₁ j₂ hj₂ hval
    have hsome₁ : (P i j₁).isSome := by simpa [rowFilledCols] using hj₁
    have hsome₂ : (P i j₂).isSome := by simpa [rowFilledCols] using hj₂
    have hcell₁ : P i j₁ = some (cellValue P (i, j₁)) :=
      cellValue_spec_of_isSome (P := P) (ij := (i, j₁)) hsome₁
    have hcell₂ : P i j₂ = some (cellValue P (i, j₂)) :=
      cellValue_spec_of_isSome (P := P) (ij := (i, j₂)) hsome₂
    exact hP.1 i j₁ j₂ (cellValue P (i, j₁)) hcell₁ (by simpa [hval] using hcell₂)
  · intro a ha
    rcases (by simpa [rowSymbols] using ha) with ⟨j, hcell⟩
    have hj : j ∈ rowFilledCols P i := by simp [rowFilledCols, hcell]
    refine ⟨j, hj, ?_⟩
    have hsome : (P i j).isSome := by simp [hcell]
    have hvalue : P i j = some (cellValue P (i, j)) :=
      cellValue_spec_of_isSome (P := P) (ij := (i, j)) hsome
    exact Option.some.inj (hvalue.symm.trans hcell)

lemma rowEmptyCols_card_eq {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    (rowEmptyCols P i).card = n - rowFill P i := by
  classical
  have hcompl : rowEmptyCols P i = (Finset.univ : Finset (Fin n)) \ rowFilledCols P i := by
    ext j
    by_cases h : P i j = none
    · simp [rowEmptyCols, rowFilledCols, h]
    · cases hcell : P i j with
      | none =>
          exact False.elim (h hcell)
      | some a =>
          simp [rowEmptyCols, rowFilledCols, hcell]
  rw [hcompl]
  have hsub : rowFilledCols P i ⊆ (Finset.univ : Finset (Fin n)) := by
    intro j _; simp
  rw [Finset.card_sdiff_of_subset hsub]
  simp [rowFilledCols_card_eq_rowFill]

lemma rowFill_le_order {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    rowFill P i ≤ n := by
  rw [← rowFilledCols_card_eq_rowFill]
  calc
    (rowFilledCols P i).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_univ _
    _ = n := by simp

lemma rowsUsed_card_eq_positive_rowFill {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) :
    (rowsUsed P).card =
      ((Finset.univ : Finset (Fin n)).filter fun i => 0 < rowFill P i).card := by
  congr 1
  ext i
  simpa using (rowFill_pos_iff_mem_rowsUsed P i).symm

lemma rowFill_relabelRows {n : ℕ} (σ : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    rowFill (relabelPartial σ (Equiv.refl (Fin n)) (Equiv.refl (Fin n)) P) i =
      rowFill P (σ i) := by
  rw [← rowFilledCols_card_eq_rowFill, ← rowFilledCols_card_eq_rowFill]
  congr 1
  ext j
  simp [rowFilledCols, relabelPartial]



lemma rowSymbolConjugate_eq_some_iff {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P)
    (e c r : Fin n) :
    rowSymbolConjugate P e c = some r ↔ P r c = some e := by
  classical
  unfold rowSymbolConjugate
  constructor
  · intro h
    by_cases hex : ∃ r, P r c = some e
    · have hchoose : Classical.choose hex = r := Option.some.inj (by simpa [hex] using h)
      have hspec : P (Classical.choose hex) c = some e := Classical.choose_spec hex
      simpa [hchoose] using hspec
    · simp [hex] at h
  · intro hcell
    have hex : ∃ r, P r c = some e := ⟨r, hcell⟩
    have hchoose : Classical.choose hex = r :=
      hP.2 (Classical.choose hex) r c e (Classical.choose_spec hex) hcell
    simp [hex, hchoose]

lemma isPartialLatin_rowSymbolConjugate {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P) :
    IsPartialLatin (rowSymbolConjugate P) := by
  constructor
  · intro e c₁ c₂ r h₁ h₂
    have h₁P : P r c₁ = some e :=
      (rowSymbolConjugate_eq_some_iff hP e c₁ r).mp h₁
    have h₂P : P r c₂ = some e :=
      (rowSymbolConjugate_eq_some_iff hP e c₂ r).mp h₂
    exact hP.1 r c₁ c₂ e h₁P h₂P
  · intro e₁ e₂ c r h₁ h₂
    have h₁P : P r c = some e₁ :=
      (rowSymbolConjugate_eq_some_iff hP e₁ c r).mp h₁
    have h₂P : P r c = some e₂ :=
      (rowSymbolConjugate_eq_some_iff hP e₂ c r).mp h₂
    exact Option.some.inj (h₁P.symm.trans h₂P)

lemma rowsUsed_rowSymbolConjugate {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P) :
    rowsUsed (rowSymbolConjugate P) = elementsUsed P := by
  classical
  ext e
  constructor
  · intro he
    rcases (by simpa [rowsUsed] using he) with ⟨c, r, hcell⟩
    have hPcell : P r c = some e :=
      (rowSymbolConjugate_eq_some_iff hP e c r).mp hcell
    exact mem_elementsUsed_of_cell hPcell
  · intro he
    rcases (by simpa [elementsUsed] using he) with ⟨r, c, hcell⟩
    have hconj : rowSymbolConjugate P e c = some r :=
      (rowSymbolConjugate_eq_some_iff hP e c r).mpr hcell
    exact mem_rowsUsed_of_cell hconj

lemma filledCells_rowSymbolConjugate_card {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P) :
    (filledCells (rowSymbolConjugate P)).card = (filledCells P).card := by
  classical
  let Q := rowSymbolConjugate P
  refine Finset.card_bij
    (fun ec _ => (cellValue Q ec, ec.2)) ?hmem ?hinj ?hsurj
  · intro ec hec
    have hsome : (Q ec.1 ec.2).isSome := by
      simpa [Q, filledCells] using hec
    have hQcell : Q ec.1 ec.2 = some (cellValue Q ec) :=
      cellValue_spec_of_isSome hsome
    have hPcell : P (cellValue Q ec) ec.2 = some ec.1 := by
      simpa [Q] using (rowSymbolConjugate_eq_some_iff hP ec.1 ec.2 (cellValue Q ec)).mp hQcell
    simp [filledCells, hPcell]
  · intro ec hec e'c' he'c' hmap
    have hsome : (Q ec.1 ec.2).isSome := by
      simpa [Q, filledCells] using hec
    have hsome' : (Q e'c'.1 e'c'.2).isSome := by
      simpa [Q, filledCells] using he'c'
    have hQcell : Q ec.1 ec.2 = some (cellValue Q ec) :=
      cellValue_spec_of_isSome hsome
    have hQcell' : Q e'c'.1 e'c'.2 = some (cellValue Q e'c') :=
      cellValue_spec_of_isSome hsome'
    have hmap' : (cellValue Q ec, ec.2) = (cellValue Q e'c', e'c'.2) := by
      simpa using hmap
    have hrow : cellValue Q ec = cellValue Q e'c' :=
      (Prod.ext_iff.mp hmap').1
    have hcol : ec.2 = e'c'.2 :=
      (Prod.ext_iff.mp hmap').2
    have hPcell : P (cellValue Q ec) ec.2 = some ec.1 := by
      simpa [Q] using (rowSymbolConjugate_eq_some_iff hP ec.1 ec.2 (cellValue Q ec)).mp hQcell
    have hPcell' : P (cellValue Q ec) ec.2 = some e'c'.1 := by
      have htmp : P (cellValue Q e'c') e'c'.2 = some e'c'.1 := by
        simpa [Q] using
          (rowSymbolConjugate_eq_some_iff hP e'c'.1 e'c'.2 (cellValue Q e'c')).mp hQcell'
      simpa [hrow, hcol] using htmp
    have heq : ec.1 = e'c'.1 := Option.some.inj (hPcell.symm.trans hPcell')
    exact Prod.ext heq hcol
  · intro rc hrc
    have hsome : (P rc.1 rc.2).isSome := by simpa [filledCells] using hrc
    let e := cellValue P rc
    have hPcell : P rc.1 rc.2 = some e := by
      dsimp [e]
      exact cellValue_spec_of_isSome hsome
    let ec : Fin n × Fin n := (e, rc.2)
    have hQcell : Q ec.1 ec.2 = some rc.1 := by
      dsimp [Q, ec, e]
      exact (rowSymbolConjugate_eq_some_iff hP (cellValue P rc) rc.2 rc.1).mpr hPcell
    have hec : ec ∈ filledCells Q := by
      simp [filledCells, hQcell]
    refine ⟨ec, hec, ?_⟩
    have hsomeQ : (Q ec.1 ec.2).isSome := by simp [hQcell]
    have hQvalue : cellValue Q ec = rc.1 := by
      have hspec := cellValue_spec_of_isSome hsomeQ
      exact Option.some.inj (hspec.symm.trans hQcell)
    simp [ec, hQvalue]



lemma rowSymbolConjugateSquare_spec {n : ℕ}
    {L : Fin n → Fin n → Fin n}
    (hcol : ∀ c : Fin n, Function.Injective fun r : Fin n => L r c)
    (a c : Fin n) :
    L (rowSymbolConjugateSquare L hcol a c) c = a :=
  Classical.choose_spec ((hcol c).surjective_of_finite (Equiv.refl (Fin n)) a)

lemma isLatinSquare_rowSymbolConjugateSquare {n : ℕ}
    {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) :
    IsLatinSquare (rowSymbolConjugateSquare L hL.2) := by
  constructor
  · intro a c₁ c₂ h
    have h₁ : L (rowSymbolConjugateSquare L hL.2 a c₁) c₁ = a :=
      rowSymbolConjugateSquare_spec hL.2 a c₁
    have h₂ : L (rowSymbolConjugateSquare L hL.2 a c₂) c₂ = a :=
      rowSymbolConjugateSquare_spec hL.2 a c₂
    have hsame : L (rowSymbolConjugateSquare L hL.2 a c₁) c₁ =
        L (rowSymbolConjugateSquare L hL.2 a c₁) c₂ := by
      rw [h₁]
      rw [h]
      exact h₂.symm
    exact hL.1 (rowSymbolConjugateSquare L hL.2 a c₁) hsame
  · intro c a₁ a₂ h
    have h₁ : L (rowSymbolConjugateSquare L hL.2 a₁ c) c = a₁ :=
      rowSymbolConjugateSquare_spec hL.2 a₁ c
    have h₂ : L (rowSymbolConjugateSquare L hL.2 a₂ c) c = a₂ :=
      rowSymbolConjugateSquare_spec hL.2 a₂ c
    calc
      a₁ = L (rowSymbolConjugateSquare L hL.2 a₁ c) c := h₁.symm
      _ = L (rowSymbolConjugateSquare L hL.2 a₂ c) c := by
        simpa using congrArg (fun x => L x c) h
      _ = a₂ := h₂



lemma completes_of_rowSymbolConjugate {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} {L : Fin n → Fin n → Fin n}
    (hP : IsPartialLatin P) (hL : Completes (rowSymbolConjugate P) L) :
    Completes P (rowSymbolConjugateSquare L hL.1.2) := by
  constructor
  · exact isLatinSquare_rowSymbolConjugateSquare hL.1
  · intro r c a hcell
    have hconj : rowSymbolConjugate P a c = some r :=
      (rowSymbolConjugate_eq_some_iff hP a c r).mpr hcell
    have hLcell : L a c = r := hL.2 a c r hconj
    have hspec := rowSymbolConjugateSquare_spec hL.1.2 r c
    exact hL.1.2 c (by simpa using hspec.trans hLcell.symm)

theorem latin_rectangle_complete {r n : ℕ} (R : Fin r → Fin n → Fin n)
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







lemma rowsLT_card {n t : ℕ} (ht : t ≤ n) :
    (rowsLT n t).card = t := by
  classical
  have hcard :
      (rowsLT n t).card = (Finset.range t).card := by
    refine Finset.card_bij (fun i _ => i.val) ?hmem ?hinj ?hsurj
    · intro i hi
      simpa [rowsLT] using hi
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro k hk
      have hkt : k < t := by simpa using hk
      have hkn : k < n := lt_of_lt_of_le hkt ht
      refine ⟨⟨k, hkn⟩, ?_, rfl⟩
      simp [rowsLT, hkt]
  simpa using hcard

lemma rowsBetween_card {n lo hi : ℕ} (hlohi : lo + 1 ≤ hi) (hhi : hi ≤ n) :
    (rowsBetween n lo hi).card = hi - (lo + 1) := by
  classical
  have hcard :
      (rowsBetween n lo hi).card = (Finset.range (hi - (lo + 1))).card := by
    refine Finset.card_bij (fun i _ => i.val - (lo + 1)) ?hmem ?hinj ?hsurj
    · intro i hirow
      have hbetween : lo < i.val ∧ i.val < hi := by
        simpa [rowsBetween] using hirow
      have hlo : lo < i.val := hbetween.1
      have hlt : i.val < hi := hbetween.2
      simp
      omega
    · intro i hirow j hjrow hij
      have hbetween_i : lo < i.val ∧ i.val < hi := by
        simpa [rowsBetween] using hirow
      have hbetween_j : lo < j.val ∧ j.val < hi := by
        simpa [rowsBetween] using hjrow
      have hlei : lo + 1 ≤ i.val := Nat.succ_le_of_lt hbetween_i.1
      have hlej : lo + 1 ≤ j.val := Nat.succ_le_of_lt hbetween_j.1
      have hsubeq : i.val - (lo + 1) = j.val - (lo + 1) := by
        simpa using hij
      have : i.val = j.val := by
        calc
          i.val = i.val - (lo + 1) + (lo + 1) := (Nat.sub_add_cancel hlei).symm
          _ = j.val - (lo + 1) + (lo + 1) := by rw [hsubeq]
          _ = j.val := Nat.sub_add_cancel hlej
      exact Fin.ext this
    · intro k hk
      have hklt : k < hi - (lo + 1) := by simpa using hk
      let v := k + (lo + 1)
      have hvn : v < n := by
        dsimp [v]
        omega
      refine ⟨⟨v, hvn⟩, ?_, ?_⟩
      · simp [rowsBetween, v]
        omega
      · dsimp [v]
        omega
  simpa using hcard

lemma rowCells_subset_filledCells {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    rowCells P i ⊆ filledCells P := by
  intro ij hij
  exact (Finset.mem_filter.mp hij).1

lemma rowCells_disjoint_of_ne {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i k : Fin n} (hik : i ≠ k) :
    Disjoint (rowCells P i) (rowCells P k) := by
  rw [Finset.disjoint_left]
  intro ij hij hikmem
  have hi : ij.1 = i := (Finset.mem_filter.mp hij).2
  have hk : ij.1 = k := (Finset.mem_filter.mp hikmem).2
  exact hik (hi.symm.trans hk)

lemma rowCells_pairwiseDisjoint {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (rows : Finset (Fin n)) :
    (rows : Set (Fin n)).PairwiseDisjoint fun i => rowCells P i := by
  intro i _hi k _hk hik
  exact rowCells_disjoint_of_ne P hik

lemma cellsInRows_card {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (rows : Finset (Fin n)) :
    (cellsInRows P rows).card = ∑ i ∈ rows, rowFill P i := by
  classical
  rw [cellsInRows, Finset.card_biUnion (rowCells_pairwiseDisjoint P rows)]
  simp [rowFill]

lemma cellsInRows_subset_filledCells {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (rows : Finset (Fin n)) :
    cellsInRows P rows ⊆ filledCells P := by
  intro ij hij
  rcases Finset.mem_biUnion.mp hij with ⟨i, _hi, hijrow⟩
  exact rowCells_subset_filledCells P i hijrow





lemma rowCells_disjoint_cellsInRows_of_notMem {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i : Fin n} {rows : Finset (Fin n)}
    (hi : i ∉ rows) : Disjoint (rowCells P i) (cellsInRows P rows) := by
  rw [Finset.disjoint_left]
  intro ij hij hijrows
  rcases Finset.mem_biUnion.mp hijrows with ⟨k, hk, hijk⟩
  have hrowi : ij.1 = i := (Finset.mem_filter.mp hij).2
  have hrowk : ij.1 = k := (Finset.mem_filter.mp hijk).2
  exact hi (by simpa [hrowi.symm.trans hrowk] using hk)

lemma cellsInRows_disjoint_of_disjoint_rows {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {rows₁ rows₂ : Finset (Fin n)}
    (hdisj : Disjoint rows₁ rows₂) :
    Disjoint (cellsInRows P rows₁) (cellsInRows P rows₂) := by
  rw [Finset.disjoint_left]
  intro ij hij₁ hij₂
  rcases Finset.mem_biUnion.mp hij₁ with ⟨i, hi, hiji⟩
  rcases Finset.mem_biUnion.mp hij₂ with ⟨k, hk, hijk⟩
  have hrowi : ij.1 = i := (Finset.mem_filter.mp hiji).2
  have hrowk : ij.1 = k := (Finset.mem_filter.mp hijk).2
  have hik : i = k := hrowi.symm.trans hrowk
  have hk' : i ∈ rows₂ := by simpa [hik] using hk
  exact (Finset.disjoint_left.mp hdisj) hi hk'

private lemma ryser_three_blocks_card_le_filled {n r t : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (hrn : r ≤ n) (ht : t < r) :
    (cellsInRows P (rowsLT n t)).card +
        (rowCells P (Fin.castLE hrn (⟨t, ht⟩ : Fin r))).card +
        (cellsInRows P (rowsBetween n t r)).card ≤
      (filledCells P).card := by
  classical
  let active : Fin n := Fin.castLE hrn (⟨t, ht⟩ : Fin r)
  let prev := cellsInRows P (rowsLT n t)
  let act := rowCells P active
  let tail := cellsInRows P (rowsBetween n t r)
  have hprev_act : Disjoint prev act := by
    have hnot : active ∉ rowsLT n t := by
      simp [rowsLT, active]
    exact (rowCells_disjoint_cellsInRows_of_notMem P hnot).symm
  have hprev_tail_rows : Disjoint (rowsLT n t) (rowsBetween n t r) := by
    rw [Finset.disjoint_left]
    intro i hi hbetween
    have hit : i.val < t := by simpa [rowsLT] using hi
    have hbtw : t < i.val ∧ i.val < r := by
      simpa [rowsBetween] using hbetween
    have hti : t < i.val := hbtw.1
    omega
  have hprev_tail : Disjoint prev tail :=
    cellsInRows_disjoint_of_disjoint_rows P hprev_tail_rows
  have hact_tail : Disjoint act tail := by
    have hnot : active ∉ rowsBetween n t r := by
      simp [rowsBetween, active]
    exact rowCells_disjoint_cellsInRows_of_notMem P hnot
  have hprevact_tail : Disjoint (prev ∪ act) tail := by
    rw [Finset.disjoint_left]
    intro ij hij hijtail
    rcases Finset.mem_union.mp hij with hijprev | hijact
    · exact (Finset.disjoint_left.mp hprev_tail) hijprev hijtail
    · exact (Finset.disjoint_left.mp hact_tail) hijact hijtail
  let U := (prev ∪ act) ∪ tail
  have hUsub : U ⊆ filledCells P := by
    intro ij hij
    rcases Finset.mem_union.mp hij with hp | htmem
    · rcases Finset.mem_union.mp hp with hprev | hact
      · exact cellsInRows_subset_filledCells P (rowsLT n t) hprev
      · exact rowCells_subset_filledCells P active hact
    · exact cellsInRows_subset_filledCells P (rowsBetween n t r) htmem
  have hcardU :
      U.card = prev.card + act.card + tail.card := by
    dsimp [U]
    rw [Finset.card_union_of_disjoint hprevact_tail]
    rw [Finset.card_union_of_disjoint hprev_act]
  calc
    prev.card + act.card + tail.card = U.card := hcardU.symm
    _ ≤ (filledCells P).card := Finset.card_le_card hUsub

private lemma ryser_ineq_one {n r t : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    (hrn : r ≤ n) (hrhalf : 2 * r ≤ n)
    (hcard : (filledCells P).card + 1 ≤ n)
    (hpos : ∀ i : Fin r, 0 < rowFill P (Fin.castLE hrn i))
    (hanti : Antitone fun i : Fin r => rowFill P (Fin.castLE hrn i))
    (ht : t < r) :
    n - rowFill P (Fin.castLE hrn (⟨t, ht⟩ : Fin r)) - t >
      t + (cellsInRows P (rowsBetween n t r)).card := by
  classical
  let active : Fin n := Fin.castLE hrn (⟨t, ht⟩ : Fin r)
  let f := rowFill P active
  let tail := (cellsInRows P (rowsBetween n t r)).card
  change n - f - t > t + tail
  have hfilled_lt : (filledCells P).card < n := by omega
  have hblocks :=
    ryser_three_blocks_card_le_filled P hrn ht
  have hblocks' :
      (cellsInRows P (rowsLT n t)).card + f + tail ≤ (filledCells P).card := by
    simpa [active, f, tail, rowFill] using hblocks
  by_cases hf2 : 2 ≤ f
  · have hprev_ge : 2 * t ≤ (cellsInRows P (rowsLT n t)).card := by
      rw [cellsInRows_card]
      have hsum_ge :
          ∑ i ∈ rowsLT n t, 2 ≤ ∑ i ∈ rowsLT n t, rowFill P i := by
        apply Finset.sum_le_sum
        intro i hi
        have hit : i.val < t := by simpa [rowsLT] using hi
        let ir : Fin r := ⟨i.val, by omega⟩
        let it : Fin r := ⟨t, ht⟩
        have hir_le : ir ≤ it := by
          exact Fin.le_def.mpr (by dsimp [ir, it]; omega)
        have hmono : rowFill P (Fin.castLE hrn it) ≤ rowFill P (Fin.castLE hrn ir) :=
          hanti hir_le
        have hcast : Fin.castLE hrn ir = i := Fin.ext (by rfl)
        exact le_trans hf2 (by simpa [active, f, ir, it, hcast] using hmono)
      have hcard_rows : (rowsLT n t).card = t :=
        rowsLT_card (le_trans (Nat.le_of_lt ht) hrn)
      have hconst : ∑ i ∈ rowsLT n t, 2 = 2 * t := by
        simp [hcard_rows, Nat.mul_comm]
      omega
    have hmain : 2 * t + f + tail ≤ (filledCells P).card := by omega
    omega
  · have hf_eq_one : f = 1 := by
      have hfp : 0 < f := by
        simpa [active, f] using hpos (⟨t, ht⟩ : Fin r)
      omega
    have htail_le_rows :
        tail ≤ (rowsBetween n t r).card := by
      dsimp [tail]
      rw [cellsInRows_card]
      calc
        ∑ i ∈ rowsBetween n t r, rowFill P i
            ≤ ∑ i ∈ rowsBetween n t r, 1 := by
          apply Finset.sum_le_sum
          intro i hi
          have hbetween : t < i.val ∧ i.val < r := by
            simpa [rowsBetween] using hi
          let ir : Fin r := ⟨i.val, hbetween.2⟩
          let it : Fin r := ⟨t, ht⟩
          have hit_le : it ≤ ir := by
            exact Fin.le_def.mpr (by dsimp [ir, it]; omega)
          have hmono : rowFill P (Fin.castLE hrn ir) ≤ rowFill P (Fin.castLE hrn it) :=
            hanti hit_le
          have hcast : Fin.castLE hrn ir = i := Fin.ext (by rfl)
          have hmono' : rowFill P i ≤ f := by
            simpa [active, f, ir, it, hcast] using hmono
          omega
        _ = (rowsBetween n t r).card := by simp
    have hrows_card : (rowsBetween n t r).card = r - (t + 1) :=
      rowsBetween_card (by omega) hrn
    have htail_bound : tail ≤ r - (t + 1) := by omega
    have hrt_lt : r + t < 2 * r := by omega
    have hrt_lt_n : r + t < n := lt_of_lt_of_le hrt_lt hrhalf
    omega



private lemma ryserStepAvailable_mem {n r t : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} {hrn : r ≤ n} {ht : t < r}
    {R : Fin t → Fin n → Fin n}
    {j : {j : Fin n // P (Fin.castLE hrn (⟨t, ht⟩ : Fin r)) j = none}}
    {a : Fin n} :
    a ∈ ryserStepAvailable P hrn ht R j ↔
      a ∉ rowSymbols P (Fin.castLE hrn (⟨t, ht⟩ : Fin r)) ∧
        (∀ i : Fin t, R i j.1 ≠ a) ∧
        (∀ k : Fin r, t < k.val → P (Fin.castLE hrn k) j.1 ≠ some a) := by
  simp [ryserStepAvailable]

private theorem ryser_row_hall_step {n r t : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) (hrn : r ≤ n) (hrhalf : 2 * r ≤ n)
    (hcard : (filledCells P).card + 1 ≤ n)
    (hpos : ∀ i : Fin r, 0 < rowFill P (Fin.castLE hrn i))
    (hanti : Antitone fun i : Fin r => rowFill P (Fin.castLE hrn i))
    (ht : t < r)
    (R : Fin t → Fin n → Fin n)
    (hRrow : ∀ i : Fin t, Function.Injective (R i))
    (_hRcol : ∀ j : Fin n, Function.Injective fun i : Fin t => R i j)
    (_hRext : ∀ i : Fin t, ∀ j a,
      P (Fin.castLE hrn (⟨i.val, by omega⟩ : Fin r)) j = some a → R i j = a)
    (hRavoidLower : ∀ i : Fin t, ∀ k : Fin r, i.val < k.val →
      ∀ j a, P (Fin.castLE hrn k) j = some a → R i j ≠ a) :
    ∃ row : Fin n → Fin n,
      Function.Injective row ∧
        (∀ j a, P (Fin.castLE hrn (⟨t, ht⟩ : Fin r)) j = some a → row j = a) ∧
        (∀ i : Fin t, ∀ j, row j ≠ R i j) ∧
        (∀ k : Fin r, t < k.val →
          ∀ j a, P (Fin.castLE hrn k) j = some a → row j ≠ a) := by
  classical
  let active : Fin n := Fin.castLE hrn (⟨t, ht⟩ : Fin r)
  let C := {j : Fin n // P active j = none}
  let A : C → Finset (Fin n) := fun j =>
    ryserStepAvailable P hrn ht R j
  let X : Finset (Fin n) := Finset.univ.filter fun a => a ∉ rowSymbols P active
  let f := rowFill P active
  let tail := (cellsInRows P (rowsBetween n t r)).card
  have hineq1 : n - f - t > t + tail := by
    simpa [active, f, tail] using
      (ryser_ineq_one (P := P) hrn hrhalf hcard hpos hanti ht)
  have hXcard : X.card = n - f := by
    have hcompl : X = (Finset.univ : Finset (Fin n)) \ rowSymbols P active := by
      ext a
      simp [X]
    rw [hcompl]
    have hsub : rowSymbols P active ⊆ (Finset.univ : Finset (Fin n)) := by
      intro a _; simp
    rw [Finset.card_sdiff_of_subset hsub]
    simp [f, rowSymbols_card_eq_rowFill hP active]
  have hCcard : Fintype.card C = n - f := by
    have hfin : Fintype.card C = (rowEmptyCols P active).card := by
      let e : C ≃ {j : Fin n // j ∈ rowEmptyCols P active} := {
        toFun j := ⟨j.1, by simp [rowEmptyCols, j.2]⟩
        invFun j := ⟨j.1, by
          exact (Finset.mem_filter.mp j.2).2⟩
        left_inv j := by cases j; rfl
        right_inv j := by cases j; rfl
      }
      exact (Fintype.card_congr e).trans (Fintype.card_coe _)
    rw [hfin, rowEmptyCols_card_eq]
  have hHall : ∀ S : Finset C, S.card ≤ (S.biUnion A).card := by
    intro S
    let B := S.biUnion A
    have hBsubX : B ⊆ X := by
      intro a ha
      rcases Finset.mem_biUnion.mp ha with ⟨j, hjS, haj⟩
      have hm := (ryserStepAvailable_mem (P := P) (hrn := hrn) (ht := ht)
        (R := R) (j := j) (a := a)).mp haj
      simpa [X, active] using hm.1
    by_cases hSempty : S.card = 0
    · have hS : S = ∅ := Finset.card_eq_zero.mp hSempty
      simp [hS]
    by_contra hnot
    have hB_lt : B.card < S.card := Nat.lt_of_not_ge hnot
    let m := S.card
    have hmpos : 0 < m := by
      dsimp [m]
      exact Nat.pos_of_ne_zero hSempty
    have hm_le_nf : m ≤ n - f := by
      dsimp [m]
      calc
        S.card ≤ Fintype.card C := Finset.card_le_univ S
        _ = n - f := hCcard
    let N := n - f - t
    by_cases hsmall : m ≤ N
    · let blocked : Finset (Fin n × C) :=
        (X ×ˢ S).filter fun p => p.1 ∉ A p.2
      let above : Finset (Fin n × C) :=
        blocked.filter fun p => ∃ i : Fin t, R i p.2.1 = p.1
      let lower : Finset (Fin n × C) :=
        blocked.filter fun p =>
          ∃ k : Fin r, t < k.val ∧ P (Fin.castLE hrn k) p.2.1 = some p.1
      have hblocked_subset : blocked ⊆ above ∪ lower := by
        intro p hp
        have hpblk : p ∈ blocked := hp
        have hprod : p ∈ X ×ˢ S := (Finset.mem_filter.mp hpblk).1
        have hnotA : p.1 ∉ A p.2 := (Finset.mem_filter.mp hpblk).2
        have hx : p.1 ∈ X := (Finset.mem_product.mp hprod).1
        have hnotCond :
            ¬ ((∀ i : Fin t, R i p.2.1 ≠ p.1) ∧
              (∀ k : Fin r, t < k.val → P (Fin.castLE hrn k) p.2.1 ≠ some p.1)) := by
          intro hcond
          exact hnotA ((ryserStepAvailable_mem (P := P) (hrn := hrn) (ht := ht)
            (R := R) (j := p.2) (a := p.1)).mpr
              ⟨by simpa [X, active] using hx, hcond.1, hcond.2⟩)
        by_cases habove : ∃ i : Fin t, R i p.2.1 = p.1
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hpblk, habove⟩))
        · have hnoAbove : ∀ i : Fin t, R i p.2.1 ≠ p.1 := by
            intro i hi
            exact habove ⟨i, hi⟩
          have hlower : ∃ k : Fin r, t < k.val ∧
              P (Fin.castLE hrn k) p.2.1 = some p.1 := by
            by_contra hno
            push Not at hno
            exact hnotCond ⟨hnoAbove, hno⟩
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hpblk, hlower⟩))
      have habove_le : above.card ≤ t * m := by
        by_cases htzero : t = 0
        · have habove_empty : above = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro p hp
            rcases (Finset.mem_filter.mp hp).2 with ⟨i, _hi⟩
            exact Fin.elim0 (by simpa [htzero] using i)
          simp [habove_empty, htzero]
        · have htpos : 0 < t := Nat.pos_of_ne_zero htzero
          let defaultI : Fin t := ⟨0, htpos⟩
          let aboveMap : Fin n × C → Fin t × C := fun p =>
            if h : ∃ i : Fin t, R i p.2.1 = p.1 then (Classical.choose h, p.2)
            else (defaultI, p.2)
          have hle :=
            Finset.card_le_card_of_injOn aboveMap
              (s := above) (t := (Finset.univ : Finset (Fin t)) ×ˢ S)
              (by
                intro p hp
                have hpabove : ∃ i : Fin t, R i p.2.1 = p.1 := (Finset.mem_filter.mp hp).2
                have hpblocked : p ∈ blocked := (Finset.mem_filter.mp hp).1
                have hpS : p.2 ∈ S := (Finset.mem_product.mp (Finset.mem_filter.mp hpblocked).1).2
                simp [aboveMap, hpabove, hpS])
              (by
                intro p hp q hq hmap
                have hpabove : ∃ i : Fin t, R i p.2.1 = p.1 := (Finset.mem_filter.mp hp).2
                have hqabove : ∃ i : Fin t, R i q.2.1 = q.1 := (Finset.mem_filter.mp hq).2
                have hmap' : (Classical.choose hpabove, p.2) =
                    (Classical.choose hqabove, q.2) := by
                  simpa [aboveMap, hpabove, hqabove] using hmap
                have hi : Classical.choose hpabove = Classical.choose hqabove :=
                  (Prod.ext_iff.mp hmap').1
                have hj : p.2 = q.2 := (Prod.ext_iff.mp hmap').2
                have hpval : R (Classical.choose hpabove) p.2.1 = p.1 :=
                  Classical.choose_spec hpabove
                have hqval : R (Classical.choose hqabove) q.2.1 = q.1 :=
                  Classical.choose_spec hqabove
                have ha : p.1 = q.1 := by
                  rw [← hpval, hi, hj, hqval]
                exact Prod.ext ha hj)
          simpa [m] using hle
      have hlower_le : lower.card ≤ tail := by
        let defaultK : Fin r := ⟨0, by omega⟩
        let lowerMap : Fin n × C → Fin n × Fin n := fun p =>
          if h : ∃ k : Fin r, t < k.val ∧ P (Fin.castLE hrn k) p.2.1 = some p.1 then
            (Fin.castLE hrn (Classical.choose h), p.2.1)
          else (Fin.castLE hrn defaultK, p.2.1)
        refine Finset.card_le_card_of_injOn
          lowerMap ?hmem ?hinj
        · intro p hp
          have hlow : ∃ k : Fin r, t < k.val ∧ P (Fin.castLE hrn k) p.2.1 = some p.1 :=
            (Finset.mem_filter.mp hp).2
          have hkspec := Classical.choose_spec hlow
          have hcell : P (Fin.castLE hrn (Classical.choose hlow)) p.2.1 = some p.1 := hkspec.2
          have hrowmem : Fin.castLE hrn (Classical.choose hlow) ∈ rowsBetween n t r := by
            simp [rowsBetween, hkspec.1]
          have hrowcell : (Fin.castLE hrn (Classical.choose hlow), p.2.1) ∈
              rowCells P (Fin.castLE hrn (Classical.choose hlow)) := by
            simp [rowCells, filledCells, hcell]
          have hmemCell :
              (Fin.castLE hrn (Classical.choose hlow), p.2.1) ∈
                cellsInRows P (rowsBetween n t r) := by
            unfold cellsInRows
            exact Finset.mem_biUnion.mpr
              ⟨Fin.castLE hrn (Classical.choose hlow), hrowmem, hrowcell⟩
          simpa [lowerMap, hlow] using hmemCell
        · intro p hp q hq hmap
          have hlowp : ∃ k : Fin r, t < k.val ∧ P (Fin.castLE hrn k) p.2.1 = some p.1 :=
            (Finset.mem_filter.mp hp).2
          have hlowq : ∃ k : Fin r, t < k.val ∧ P (Fin.castLE hrn k) q.2.1 = some q.1 :=
            (Finset.mem_filter.mp hq).2
          have hmap' :
              (Fin.castLE hrn (Classical.choose hlowp), p.2.1) =
                (Fin.castLE hrn (Classical.choose hlowq), q.2.1) := by
            simpa [lowerMap, hlowp, hlowq] using hmap
          have hrow :
              Fin.castLE hrn (Classical.choose hlowp) =
                Fin.castLE hrn (Classical.choose hlowq) := (Prod.ext_iff.mp hmap').1
          have hcol : p.2.1 = q.2.1 := (Prod.ext_iff.mp hmap').2
          have hpval : P (Fin.castLE hrn (Classical.choose hlowp)) p.2.1 = some p.1 :=
            (Classical.choose_spec hlowp).2
          have hqval : P (Fin.castLE hrn (Classical.choose hlowp)) p.2.1 = some q.1 := by
            rw [hrow, hcol]
            exact (Classical.choose_spec hlowq).2
          have ha : p.1 = q.1 := Option.some.inj (hpval.symm.trans hqval)
          have hsub : p.2 = q.2 := Subtype.ext hcol
          exact Prod.ext ha hsub
      have hblocked_upper : blocked.card ≤ t * m + tail := by
        calc
          blocked.card ≤ (above ∪ lower).card := Finset.card_le_card hblocked_subset
          _ ≤ above.card + lower.card := Finset.card_union_le above lower
          _ ≤ t * m + tail := Nat.add_le_add habove_le hlower_le
      let miss := X \ B
      have hmiss_blocked : miss ×ˢ S ⊆ blocked := by
        intro p hp
        rcases Finset.mem_product.mp hp with ⟨haMiss, hjS⟩
        have haX : p.1 ∈ X := (Finset.mem_sdiff.mp haMiss).1
        have haNotB : p.1 ∉ B := (Finset.mem_sdiff.mp haMiss).2
        have hnotA : p.1 ∉ A p.2 := by
          intro hA
          exact haNotB (Finset.mem_biUnion.mpr ⟨p.2, hjS, hA⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haX, hjS⟩, hnotA⟩
      have hblocked_lower : miss.card * m ≤ blocked.card := by
        calc
          miss.card * m = (miss ×ˢ S).card := by simp [m]
          _ ≤ blocked.card := Finset.card_le_card hmiss_blocked
      have hBcard_le_X : B.card ≤ X.card := Finset.card_le_card hBsubX
      have hmiss_card : miss.card = X.card - B.card := by
        exact Finset.card_sdiff_of_subset hBsubX
      have hmiss_ge : n - f - m + 1 ≤ miss.card := by
        rw [hmiss_card, hXcard]
        omega
      have hcontra_le : (n - f - m + 1) * m ≤ t * m + tail := by
        have hmul := Nat.mul_le_mul_right m hmiss_ge
        calc
          (n - f - m + 1) * m ≤ miss.card * m := hmul
          _ ≤ blocked.card := hblocked_lower
          _ ≤ t * m + tail := hblocked_upper
      have hquad_ge : n - f - t ≤ m * (n - f - t + 1 - m) := by
        have hmleN : m ≤ n - f - t := hsmall
        have := nat_ineq (n - f - t) m hmpos hmleN
        have hterm : n - f - t - m + 1 = n - f - t + 1 - m := by omega
        simpa [Nat.mul_comm, hterm] using this
      have htail_lt_quad : tail < m * (n - f - t + 1 - m) := by
        exact lt_of_lt_of_le (by omega : tail < n - f - t) hquad_ge
      have hdecomp : n - f - m + 1 = t + (n - f - t + 1 - m) := by
        omega
      have hstrict : t * m + tail < (n - f - m + 1) * m := by
        rw [hdecomp, Nat.add_mul]
        have hcomm : (n - f - t + 1 - m) * m =
            m * (n - f - t + 1 - m) := Nat.mul_comm _ _
        rw [hcomm]
        omega
      omega
    · have hlarge : n - f - t < m := Nat.lt_of_not_ge hsmall
      have hB_eq_X : B = X := by
        apply Finset.Subset.antisymm hBsubX
        intro a haX
        by_contra haNotB
        let blockedCols : Finset C := Finset.univ.filter fun j => a ∉ A j
        have hSsub : S ⊆ blockedCols := by
          intro j hjS
          have hnotA : a ∉ A j := by
            intro hA
            exact haNotB (Finset.mem_biUnion.mpr ⟨j, hjS, hA⟩)
          simp [blockedCols, hnotA]
        have hblockedCols_le : blockedCols.card ≤ t + tail := by
          let aboveCols : Finset C := blockedCols.filter fun j => ∃ i : Fin t, R i j.1 = a
          let lowerCols : Finset C := blockedCols.filter fun j =>
            ∃ k : Fin r, t < k.val ∧ P (Fin.castLE hrn k) j.1 = some a
          have hcols_subset : blockedCols ⊆ aboveCols ∪ lowerCols := by
            intro j hj
            have hnotA : a ∉ A j := by simpa [blockedCols] using (Finset.mem_filter.mp hj).2
            have hnotCond :
                ¬ ((∀ i : Fin t, R i j.1 ≠ a) ∧
                  (∀ k : Fin r, t < k.val → P (Fin.castLE hrn k) j.1 ≠ some a)) := by
              intro hcond
              exact hnotA ((ryserStepAvailable_mem (P := P) (hrn := hrn) (ht := ht)
                (R := R) (j := j) (a := a)).mpr
                  ⟨by simpa [X, active] using haX, hcond.1, hcond.2⟩)
            by_cases habove : ∃ i : Fin t, R i j.1 = a
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hj, habove⟩))
            · have hnoAbove : ∀ i : Fin t, R i j.1 ≠ a := by
                intro i hi
                exact habove ⟨i, hi⟩
              have hlower : ∃ k : Fin r, t < k.val ∧
                  P (Fin.castLE hrn k) j.1 = some a := by
                by_contra hno
                push Not at hno
                exact hnotCond ⟨hnoAbove, hno⟩
              exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hj, hlower⟩))
          have haboveCols_le : aboveCols.card ≤ t := by
            by_cases htzero : t = 0
            · have habove_empty : aboveCols = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro j hj
                rcases (Finset.mem_filter.mp hj).2 with ⟨i, _hi⟩
                exact Fin.elim0 (by simpa [htzero] using i)
              simp [habove_empty, htzero]
            · have htpos : 0 < t := Nat.pos_of_ne_zero htzero
              let defaultI : Fin t := ⟨0, htpos⟩
              let aboveColMap : C → Fin t := fun j =>
                if h : ∃ i : Fin t, R i j.1 = a then Classical.choose h else defaultI
              have hle :=
                Finset.card_le_card_of_injOn aboveColMap
                  (s := aboveCols) (t := (Finset.univ : Finset (Fin t)))
                  (by intro j hj; simp)
                  (by
                    intro j hj k hk hmap
                    have hjabove : ∃ i : Fin t, R i j.1 = a := (Finset.mem_filter.mp hj).2
                    have hkabove : ∃ i : Fin t, R i k.1 = a := (Finset.mem_filter.mp hk).2
                    have hmap' : Classical.choose hjabove = Classical.choose hkabove := by
                      simpa [aboveColMap, hjabove, hkabove] using hmap
                    have hjval : R (Classical.choose hjabove) j.1 = a := Classical.choose_spec hjabove
                    have hkval : R (Classical.choose hkabove) k.1 = a := Classical.choose_spec hkabove
                    have hcol_eq : j.1 = k.1 := by
                      exact hRrow (Classical.choose hjabove) (by
                        rw [hjval]
                        rw [hmap']
                        exact hkval.symm)
                    exact Subtype.ext hcol_eq)
              simpa using hle
          have hlowerCols_le : lowerCols.card ≤ tail := by
            let defaultK : Fin r := ⟨0, by omega⟩
            let lowerColMap : C → Fin n × Fin n := fun j =>
              if h : ∃ k : Fin r, t < k.val ∧ P (Fin.castLE hrn k) j.1 = some a then
                (Fin.castLE hrn (Classical.choose h), j.1)
              else (Fin.castLE hrn defaultK, j.1)
            refine Finset.card_le_card_of_injOn
              (s := lowerCols) (t := cellsInRows P (rowsBetween n t r))
              lowerColMap ?_ ?_
            · intro j hj
              have hlow : ∃ k : Fin r, t < k.val ∧ P (Fin.castLE hrn k) j.1 = some a :=
                (Finset.mem_filter.mp hj).2
              have hkspec := Classical.choose_spec hlow
              have hcell : P (Fin.castLE hrn (Classical.choose hlow)) j.1 = some a := hkspec.2
              have hrowmem : Fin.castLE hrn (Classical.choose hlow) ∈ rowsBetween n t r := by
                simp [rowsBetween, hkspec.1]
              have hrowcell : (Fin.castLE hrn (Classical.choose hlow), j.1) ∈
                  rowCells P (Fin.castLE hrn (Classical.choose hlow)) := by
                simp [rowCells, filledCells, hcell]
              have hmemCell : (Fin.castLE hrn (Classical.choose hlow), j.1) ∈
                  cellsInRows P (rowsBetween n t r) := by
                unfold cellsInRows
                exact Finset.mem_biUnion.mpr
                  ⟨Fin.castLE hrn (Classical.choose hlow), hrowmem, hrowcell⟩
              simpa [lowerColMap, hlow] using hmemCell
            · intro j hj k hk hmap
              have hlowj : ∃ k : Fin r, t < k.val ∧ P (Fin.castLE hrn k) j.1 = some a :=
                (Finset.mem_filter.mp hj).2
              have hlowk : ∃ k' : Fin r, t < k'.val ∧ P (Fin.castLE hrn k') k.1 = some a :=
                (Finset.mem_filter.mp hk).2
              have hmap' :
                  (Fin.castLE hrn (Classical.choose hlowj), j.1) =
                    (Fin.castLE hrn (Classical.choose hlowk), k.1) := by
                simpa [lowerColMap, hlowj, hlowk] using hmap
              exact Subtype.ext (Prod.ext_iff.mp hmap').2
          calc
            blockedCols.card ≤ (aboveCols ∪ lowerCols).card := Finset.card_le_card hcols_subset
            _ ≤ aboveCols.card + lowerCols.card := Finset.card_union_le aboveCols lowerCols
            _ ≤ t + tail := Nat.add_le_add haboveCols_le hlowerCols_le
        have hm_le_blockedCols : m ≤ blockedCols.card := by
          dsimp [m]
          exact Finset.card_le_card hSsub
        omega
      have hBcard : B.card = X.card := by rw [hB_eq_X]
      omega
  obtain ⟨choice, hchoice_inj, hchoice_mem⟩ := hall_system_of_distinct_representatives A hHall
  let row : Fin n → Fin n := fun j =>
    if h : P active j = none then choice ⟨j, h⟩ else cellValue P (active, j)
  have hrow_fixed : ∀ j a, P active j = some a → row j = a := by
    intro j a hcell
    have hnot : ¬ P active j = none := by simp [hcell]
    have hsome : (P active j).isSome := by simp [hcell]
    have hvalue : P active j = some (cellValue P (active, j)) :=
      cellValue_spec_of_isSome (P := P) (ij := (active, j)) hsome
    have hval : cellValue P (active, j) = a := Option.some.inj (hvalue.symm.trans hcell)
    simp [row, hnot, hval]
  have hrow_empty_mem : ∀ j (h : P active j = none),
      choice ⟨j, h⟩ ∈ X ∧
        (∀ i : Fin t, R i j ≠ choice ⟨j, h⟩) ∧
        (∀ k : Fin r, t < k.val → P (Fin.castLE hrn k) j ≠ some (choice ⟨j, h⟩)) := by
    intro j h
    have hmem := hchoice_mem ⟨j, h⟩
    have hm := (ryserStepAvailable_mem (P := P) (hrn := hrn) (ht := ht)
      (R := R) (j := ⟨j, h⟩) (a := choice ⟨j, h⟩)).mp hmem
    exact ⟨by simpa [X, active] using hm.1, hm.2.1, hm.2.2⟩
  have hrow_inj : Function.Injective row := by
    intro j₁ j₂ hEq
    by_cases h₁ : P active j₁ = none
    · by_cases h₂ : P active j₂ = none
      · have hchoice : choice ⟨j₁, h₁⟩ = choice ⟨j₂, h₂⟩ := by
          simpa [row, h₁, h₂] using hEq
        exact congrArg Subtype.val (hchoice_inj hchoice)
      · cases hcell₂ : P active j₂ with
        | none => exact False.elim (h₂ hcell₂)
        | some a₂ =>
            have hrow₂ : row j₂ = a₂ := hrow_fixed j₂ a₂ hcell₂
            have hchoice_not_row : choice ⟨j₁, h₁⟩ ∉ rowSymbols P active :=
              by simpa [X] using (hrow_empty_mem j₁ h₁).1
            have hchoice_eq : choice ⟨j₁, h₁⟩ = a₂ := by
              simpa [row, h₁, hrow₂] using hEq
            have ha₂row : a₂ ∈ rowSymbols P active := by
              simp [rowSymbols]
              exact ⟨j₂, hcell₂⟩
            exact False.elim (hchoice_not_row (by simpa [hchoice_eq] using ha₂row))
    · by_cases h₂ : P active j₂ = none
      · cases hcell₁ : P active j₁ with
        | none => exact False.elim (h₁ hcell₁)
        | some a₁ =>
            have hrow₁ : row j₁ = a₁ := hrow_fixed j₁ a₁ hcell₁
            have hchoice_not_row : choice ⟨j₂, h₂⟩ ∉ rowSymbols P active :=
              by simpa [X] using (hrow_empty_mem j₂ h₂).1
            have hchoice_eq : a₁ = choice ⟨j₂, h₂⟩ := by
              simpa [row, h₂, hrow₁] using hEq
            have ha₁row : a₁ ∈ rowSymbols P active := by
              simp [rowSymbols]
              exact ⟨j₁, hcell₁⟩
            exact False.elim (hchoice_not_row (by simpa [hchoice_eq] using ha₁row))
      · cases hcell₁ : P active j₁ with
        | none => exact False.elim (h₁ hcell₁)
        | some a₁ =>
            cases hcell₂ : P active j₂ with
            | none => exact False.elim (h₂ hcell₂)
            | some a₂ =>
                have hrow₁ : row j₁ = a₁ := hrow_fixed j₁ a₁ hcell₁
                have hrow₂ : row j₂ = a₂ := hrow_fixed j₂ a₂ hcell₂
                have ha : a₁ = a₂ := by
                  rw [← hrow₁, hEq, hrow₂]
                exact hP.1 active j₁ j₂ a₁ hcell₁ (by simpa [ha] using hcell₂)
  have habove : ∀ i : Fin t, ∀ j, row j ≠ R i j := by
    intro i j
    by_cases hj : P active j = none
    · intro heq
      have hrowj : row j = choice ⟨j, hj⟩ := by simp [row, hj]
      exact (hrow_empty_mem j hj).2.1 i (by rw [← hrowj]; exact heq.symm)
    · cases hcell : P active j with
      | none => exact False.elim (hj hcell)
      | some a =>
          have hrowj : row j = a := hrow_fixed j a hcell
          have havoid := hRavoidLower i (⟨t, ht⟩ : Fin r) i.isLt j a (by simpa [active] using hcell)
          intro heq
          exact havoid (by rw [hrowj] at heq; exact heq.symm)
  have hbelow : ∀ k : Fin r, t < k.val →
      ∀ j a, P (Fin.castLE hrn k) j = some a → row j ≠ a := by
    intro k hk j a hcell
    by_cases hj : P active j = none
    · have hnot := (hrow_empty_mem j hj).2.2 k hk
      intro heq
      have hchoice_eq : choice ⟨j, hj⟩ = a := by
        simpa [row, hj] using heq
      exact hnot (by simpa [hchoice_eq] using hcell)
    · cases hactive_cell : P active j with
      | none => exact False.elim (hj hactive_cell)
      | some b =>
          have hrowj : row j = b := hrow_fixed j b hactive_cell
          have hneqrow : active ≠ Fin.castLE hrn k := by
            intro heq
            have hv := congrArg Fin.val heq
            dsimp [active] at hv
            omega
          have hcolneq : b ≠ a := by
            intro hba
            have hsame : active = Fin.castLE hrn k :=
              hP.2 active (Fin.castLE hrn k) j b hactive_cell (by simpa [hba] using hcell)
            exact hneqrow hsame
          intro heq
          exact hcolneq (by rw [hrowj] at heq; exact heq)
  exact ⟨row, hrow_inj, by simpa [active] using hrow_fixed, habove, hbelow⟩

private theorem ryser_complete_sorted_top_rows {n r : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) (hrn : r ≤ n) (hrhalf : 2 * r ≤ n)
    (hcard : (filledCells P).card + 1 ≤ n)
    (hpos : ∀ i : Fin r, 0 < rowFill P (Fin.castLE hrn i))
    (hanti : Antitone fun i : Fin r => rowFill P (Fin.castLE hrn i)) :
    ∃ R : Fin r → Fin n → Fin n,
      (∀ i : Fin r, Function.Injective (R i)) ∧
      (∀ j : Fin n, Function.Injective fun i : Fin r => R i j) ∧
      (∀ i : Fin r, ∀ j a, P (Fin.castLE hrn i) j = some a → R i j = a) := by
  classical
  let motive : ℕ → Prop := fun t =>
    ∀ htr : t ≤ r,
      ∃ R : Fin t → Fin n → Fin n,
        (∀ i : Fin t, Function.Injective (R i)) ∧
        (∀ j : Fin n, Function.Injective fun i : Fin t => R i j) ∧
        (∀ i : Fin t, ∀ j a,
          P (Fin.castLE hrn (⟨i.val, by omega⟩ : Fin r)) j = some a → R i j = a) ∧
        (∀ i : Fin t, ∀ k : Fin r, i.val < k.val →
          ∀ j a, P (Fin.castLE hrn k) j = some a → R i j ≠ a)
  have step : ∀ t, (∀ u < t, motive u) → motive t := by
    intro t ih htr
    by_cases ht0 : t = 0
    · subst t
      let R0 : Fin 0 → Fin n → Fin n := fun i => Fin.elim0 i
      refine ⟨R0, ?_, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro j i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
    · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
      let s := t - 1
      have hs_lt_t : s < t := by
        dsimp [s]
        omega
      have hs_lt_r : s < r := by
        dsimp [s]
        omega
      have hs_le_r : s ≤ r := Nat.le_of_lt hs_lt_r
      obtain ⟨R, hRrow, hRcol, hRext, hRavoid⟩ := ih s hs_lt_t hs_le_r
      obtain ⟨newRow, hnewInj, hnewExt, hnewAbove, hnewBelow⟩ :=
        ryser_row_hall_step (P := P) hP hrn hrhalf hcard hpos hanti hs_lt_r
          R hRrow hRcol hRext hRavoid
      let Rplus : Fin t → Fin n → Fin n := fun i j =>
        if hi : i.val < s then R ⟨i.val, hi⟩ j else newRow j
      have hrowPlus : ∀ i : Fin t, Function.Injective (Rplus i) := by
        intro i j₁ j₂ h
        by_cases hi : i.val < s
        · have hR : R ⟨i.val, hi⟩ j₁ = R ⟨i.val, hi⟩ j₂ := by
            simpa [Rplus, hi] using h
          exact hRrow ⟨i.val, hi⟩ hR
        · have hn : newRow j₁ = newRow j₂ := by
            simpa [Rplus, hi] using h
          exact hnewInj hn
      have hcolPlus : ∀ j : Fin n, Function.Injective fun i : Fin t => Rplus i j := by
        intro j i₁ i₂ h
        by_cases h₁ : i₁.val < s
        · by_cases h₂ : i₂.val < s
          · have hR : R ⟨i₁.val, h₁⟩ j = R ⟨i₂.val, h₂⟩ j := by
              simpa [Rplus, h₁, h₂] using h
            have hii : (⟨i₁.val, h₁⟩ : Fin s) = ⟨i₂.val, h₂⟩ := hRcol j hR
            exact Fin.ext (by simpa using congrArg Fin.val hii)
          · have hbad : R ⟨i₁.val, h₁⟩ j = newRow j := by
              simpa [Rplus, h₁, h₂] using h
            exact False.elim (hnewAbove ⟨i₁.val, h₁⟩ j hbad.symm)
        · by_cases h₂ : i₂.val < s
          · have hbad : newRow j = R ⟨i₂.val, h₂⟩ j := by
              simpa [Rplus, h₁, h₂] using h
            exact False.elim (hnewAbove ⟨i₂.val, h₂⟩ j hbad)
          · have hi₁ : i₁.val = s := by
              have hi₁lt : i₁.val < t := i₁.isLt
              dsimp [s] at h₁ ⊢
              omega
            have hi₂ : i₂.val = s := by
              have hi₂lt : i₂.val < t := i₂.isLt
              dsimp [s] at h₂ ⊢
              omega
            exact Fin.ext (hi₁.trans hi₂.symm)
      have hExtPlus : ∀ i : Fin t, ∀ j a,
          P (Fin.castLE hrn (⟨i.val, by omega⟩ : Fin r)) j = some a →
            Rplus i j = a := by
        intro i j a hcell
        by_cases hi : i.val < s
        · have hcast : (⟨(⟨i.val, hi⟩ : Fin s).val, by omega⟩ : Fin r) =
              (⟨i.val, by omega⟩ : Fin r) := rfl
          simpa [Rplus, hi, hcast] using hRext ⟨i.val, hi⟩ j a hcell
        · have hival : i.val = s := by
            have hilt : i.val < t := i.isLt
            dsimp [s] at hi ⊢
            omega
          have hroweq : Fin.castLE hrn (⟨i.val, by omega⟩ : Fin r) =
              Fin.castLE hrn (⟨s, hs_lt_r⟩ : Fin r) := by
            exact Fin.ext (by simp [hival])
          have hcell' : P (Fin.castLE hrn (⟨s, hs_lt_r⟩ : Fin r)) j = some a := by
            simpa [hroweq] using hcell
          have hnew := hnewExt j a hcell'
          simp [Rplus, hi, hnew]
      have hAvoidPlus : ∀ i : Fin t, ∀ k : Fin r, i.val < k.val →
          ∀ j a, P (Fin.castLE hrn k) j = some a → Rplus i j ≠ a := by
        intro i k hik j a hcell
        by_cases hi : i.val < s
        · exact by
            simpa [Rplus, hi] using hRavoid ⟨i.val, hi⟩ k hik j a hcell
        · have hival : i.val = s := by
            have hilt : i.val < t := i.isLt
            dsimp [s] at hi ⊢
            omega
          have hsk : s < k.val := by omega
          exact by
            simpa [Rplus, hi] using hnewBelow k hsk j a hcell
      exact ⟨Rplus, hrowPlus, hcolPlus, hExtPlus, hAvoidPlus⟩
  obtain ⟨R, hRrow, hRcol, hRext, _hAvoid⟩ :=
    (Nat.strong_induction_on (p := motive) r step) (le_rfl)
  exact ⟨R, hRrow, hRcol, by
    intro i j a hcell
    simpa using hRext i j a hcell⟩

private theorem ryser_sorted_top_rows_completes {n r : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) (hrn : r ≤ n) (hrhalf : 2 * r ≤ n)
    (hcard : (filledCells P).card + 1 ≤ n)
    (hpos : ∀ i : Fin r, 0 < rowFill P (Fin.castLE hrn i))
    (hanti : Antitone fun i : Fin r => rowFill P (Fin.castLE hrn i))
    (houtside : ∀ i : Fin n, r ≤ i.val → ∀ j, P i j = none) :
    ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  classical
  obtain ⟨R, hRrow, hRcol, hRext⟩ :=
    ryser_complete_sorted_top_rows (P := P) hP hrn hrhalf hcard hpos hanti
  obtain ⟨L, hLatin, hRect⟩ := latin_rectangle_complete R hRrow hRcol hrn
  refine ⟨L, ⟨hLatin, ?_⟩⟩
  intro i j a hcell
  by_cases hi : i.val < r
  · let ir : Fin r := ⟨i.val, hi⟩
    have hcast : Fin.castLE hrn ir = i := Fin.ext (by rfl)
    have hR : R ir j = a := by
      exact hRext ir j a (by simpa [hcast] using hcell)
    calc
      L i j = L (Fin.castLE hrn ir) j := by rw [hcast]
      _ = R ir j := hRect ir j
      _ = a := hR
  · have hnone := houtside i (Nat.le_of_not_gt hi) j
    rw [hnone] at hcell
    cases hcell

private theorem ryser_rows_used_completes {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) (hcard : (filledCells P).card + 1 ≤ n)
    (hrows : 2 * (rowsUsed P).card ≤ n) :
    ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  classical
  let r := (rowsUsed P).card
  have hrn : r ≤ n := by omega
  let score : Fin n → ℕ := fun i => n - rowFill P i
  let σ : Equiv.Perm (Fin n) := Tuple.sort score
  let P' : Fin n → Fin n → Option (Fin n) :=
    relabelPartial σ (Equiv.refl (Fin n)) (Equiv.refl (Fin n)) P
  have hP' : IsPartialLatin P' := by
    dsimp [P']
    exact isPartialLatin_relabelPartial σ (Equiv.refl (Fin n)) (Equiv.refl (Fin n)) hP
  have hcard' : (filledCells P').card + 1 ≤ n := by
    dsimp [P']
    rw [filledCells_relabelPartial_card]
    exact hcard
  have hscore_mono : Monotone fun i : Fin n => score (σ i) := by
    simpa [σ] using Tuple.monotone_sort score
  have hfill_anti_orig : Antitone fun i : Fin n => rowFill P (σ i) := by
    intro i j hij
    have hs := hscore_mono hij
    have hi_le := rowFill_le_order P (σ i)
    have hj_le := rowFill_le_order P (σ j)
    dsimp [score] at hs
    have hs_int : ((n - rowFill P (σ i) : ℕ) : ℤ) ≤
        ((n - rowFill P (σ j) : ℕ) : ℤ) := by
      exact_mod_cast hs
    rw [Int.ofNat_sub hi_le, Int.ofNat_sub hj_le] at hs_int
    have hle_int : (rowFill P (σ j) : ℤ) ≤ (rowFill P (σ i) : ℤ) := by
      linarith
    exact_mod_cast hle_int
  have hfill_anti :
      Antitone fun i : Fin r => rowFill P' (Fin.castLE hrn i) := by
    intro i j hij
    have hle := hfill_anti_orig (show Fin.castLE hrn i ≤ Fin.castLE hrn j from by
      exact Fin.le_def.mpr (by simpa [Fin.castLE] using (Fin.le_def.mp hij)))
    simpa [P', rowFill_relabelRows] using hle
  let posSorted : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun i => 0 < rowFill P (σ i)
  let posOrig : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun i => 0 < rowFill P i
  have hposImage : posSorted.image σ = posOrig := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, hji⟩
      have hjpos : 0 < rowFill P (σ j) := by simpa [posSorted] using hj
      simp [posOrig, ← hji, hjpos]
    · intro hi
      have hipos : 0 < rowFill P i := by simpa [posOrig] using hi
      refine Finset.mem_image.mpr ⟨σ.symm i, ?_, by simp⟩
      simp [posSorted, hipos]
  have hposSorted_card : posSorted.card = r := by
    calc
      posSorted.card = (posSorted.image σ).card := by
        rw [Finset.card_image_of_injective]
        exact σ.injective
      _ = posOrig.card := by rw [hposImage]
      _ = r := by
        dsimp [posOrig, r]
        rw [← rowsUsed_card_eq_positive_rowFill]
  have hpos_iff : ∀ i : Fin n, i.val < r ↔ 0 < rowFill P (σ i) := by
    intro i
    have htuple :=
      Tuple.lt_card_gt_iff_apply_gt_of_antitone
        (f := fun i : Fin n => rowFill P (σ i)) (a := 0)
        (j := i) hfill_anti_orig
    simpa [posSorted, hposSorted_card] using htuple
  have hpos' : ∀ i : Fin r, 0 < rowFill P' (Fin.castLE hrn i) := by
    intro i
    have hlt : (Fin.castLE hrn i).val < r := by
      simp [Fin.castLE, i.isLt]
    have hp := (hpos_iff (Fin.castLE hrn i)).mp hlt
    simpa [P', rowFill_relabelRows] using hp
  have houtside' : ∀ i : Fin n, r ≤ i.val → ∀ j, P' i j = none := by
    intro i hi j
    have hnotpos : ¬ 0 < rowFill P (σ i) := by
      intro hp
      have hlt := (hpos_iff i).mpr hp
      omega
    have hzero : rowFill P' i = 0 := by
      have hfill : rowFill P' i = rowFill P (σ i) := by
        simpa [P'] using rowFill_relabelRows σ P i
      omega
    exact (rowFill_eq_zero_iff_row_empty P' i).mp hzero j
  obtain ⟨L', hL'⟩ :=
    ryser_sorted_top_rows_completes (P := P') hP' hrn hrows hcard' hpos' hfill_anti houtside'
  exact (completion_exists_relabelPartial_iff σ (Equiv.refl (Fin n)) (Equiv.refl (Fin n)) P).mp
    ⟨L', by simpa [P'] using hL'⟩



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

theorem solution (n : ℕ)
    (P : Fin n → Fin n → Option (Fin n)) (hP : IsPartialLatin P)
    (hcard : (filledCells P).card + 1 <= n)
    (helem : 2 * (elementsUsed P).card <= n) :
    ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  classical
  let Q := rowSymbolConjugate P
  have hQ : IsPartialLatin Q := by
    dsimp [Q]
    exact isPartialLatin_rowSymbolConjugate hP
  have hQcard : (filledCells Q).card + 1 ≤ n := by
    dsimp [Q]
    rw [filledCells_rowSymbolConjugate_card hP]
    exact hcard
  have hQrows : 2 * (rowsUsed Q).card ≤ n := by
    dsimp [Q]
    rw [rowsUsed_rowSymbolConjugate hP]
    exact helem
  obtain ⟨LQ, hLQ⟩ := ryser_rows_used_completes hQ hQcard hQrows
  exact ⟨rowSymbolConjugateSquare LQ hLQ.1.2,
    completes_of_rowSymbolConjugate hP (by simpa [Q] using hLQ)⟩
