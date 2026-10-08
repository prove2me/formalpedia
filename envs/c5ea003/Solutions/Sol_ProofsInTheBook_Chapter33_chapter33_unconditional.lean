-- Prove2me | solution 1 for ProofsInTheBook.Chapter33.chapter33_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:08:37.664691+00:00
-- url     : https://prove2.me/submissions/f5a1a259-c004-4515-aec5-49880ba5bec2

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







lemma completes_of_extendsPartial {n : ℕ} {P Q : Fin n → Fin n → Option (Fin n)}
    {L : Fin n → Fin n → Fin n} (hPQ : ExtendsPartial P Q) (hQL : Completes Q L) :
    Completes P L := by
  rcases hQL with ⟨hLatin, hcomp⟩
  exact ⟨hLatin, fun i j a hP => hcomp i j a (hPQ i j a hP)⟩

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

theorem extend_partialLatin_to_exact {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
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

/--
Reduction from the `≤ n - 1` Evans statement to the exact `= n - 1` case.

The remaining unformalized Smetaniuk frontier is therefore the exact-cardinality
case; the padding step for smaller partial squares is proved here without any
extra premise.
-/
theorem completion_from_exact_cardinality_case {n : ℕ}
    (hexact : EvansExactCardinalityCase n) :
    LatinSquareCompletionTheorem n := by
  intro P hP hfilled_le
  obtain ⟨Q, hQ, hPQ, hQcard⟩ := extend_partialLatin_to_exact hP hfilled_le
  obtain ⟨L, hL⟩ := hexact Q hQ hQcard
  exact ⟨L, completes_of_extendsPartial hPQ hL⟩

/-!
### Elementary complete orders

Squares with at most one filled cell, and orders `0`, `1`, `2`, and `3`, do not
need the Evans/Smetaniuk induction.
-/



theorem isLatinSquare_cyclicLatinSquare (n : ℕ) : IsLatinSquare (cyclicLatinSquare n) := by
  constructor
  · intro i x y h
    exact add_left_cancel h
  · intro j x y h
    exact add_right_cancel h



theorem isLatinSquare_cyclicLatinSquareWithCell {n : ℕ} (i₀ j₀ a₀ : Fin n) :
    IsLatinSquare (cyclicLatinSquareWithCell i₀ j₀ a₀) := by
  constructor
  · intro i x y h
    unfold cyclicLatinSquareWithCell at h
    have h' : i + x = i + y := (Equiv.swap (i₀ + j₀) a₀).injective h
    exact add_left_cancel h'
  · intro j x y h
    unfold cyclicLatinSquareWithCell at h
    have h' : x + j = y + j := (Equiv.swap (i₀ + j₀) a₀).injective h
    exact add_right_cancel h'

theorem cyclicLatinSquareWithCell_spec {n : ℕ} (i₀ j₀ a₀ : Fin n) :
    cyclicLatinSquareWithCell i₀ j₀ a₀ i₀ j₀ = a₀ := by
  simp [cyclicLatinSquareWithCell]

theorem latin_square_completion_card_le_one {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hfilled_le : (filledCells P).card ≤ 1) :
    ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  classical
  by_cases hfilled : ∃ i j a, P i j = some a
  · rcases hfilled with ⟨i₀, j₀, a₀, hcell₀⟩
    refine ⟨cyclicLatinSquareWithCell i₀ j₀ a₀, ?_⟩
    constructor
    · exact isLatinSquare_cyclicLatinSquareWithCell i₀ j₀ a₀
    · intro i j a hcell
      have hmem : (i, j) ∈ filledCells P := by
        simp [filledCells, hcell]
      have hmem₀ : (i₀, j₀) ∈ filledCells P := by
        simp [filledCells, hcell₀]
      have hp_eq : (i, j) = (i₀, j₀) :=
        (Finset.card_le_one_iff.mp hfilled_le) hmem hmem₀
      have hi : i = i₀ := congrArg Prod.fst hp_eq
      have hj : j = j₀ := congrArg Prod.snd hp_eq
      subst i
      subst j
      have ha : a = a₀ := by
        have hsome : some a = some a₀ := by
          rw [← hcell, hcell₀]
        exact Option.some.inj hsome
      subst a
      exact cyclicLatinSquareWithCell_spec i₀ j₀ a₀
  · refine ⟨cyclicLatinSquare n, ?_⟩
    constructor
    · exact isLatinSquare_cyclicLatinSquare n
    · intro i j a hcell
      exact False.elim (hfilled ⟨i, j, a, hcell⟩)

theorem latin_square_completion_order_zero (P : Fin 0 → Fin 0 → Option (Fin 0)) :
    ∃ L : Fin 0 → Fin 0 → Fin 0, Completes P L := by
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  simp [Completes, IsLatinSquare]

theorem latin_square_completion_order_one (P : Fin 1 → Fin 1 → Option (Fin 1)) :
    ∃ L : Fin 1 → Fin 1 → Fin 1, Completes P L := by
  refine ⟨fun _ _ => 0, ?_⟩
  constructor
  · constructor
    · intro _i x y _h
      exact Subsingleton.elim x y
    · intro _j x y _h
      exact Subsingleton.elim x y
  · intro _i _j _a _hP
    exact Subsingleton.elim _ _





private theorem isLatinSquare_latinSquareFinTwoWithCell (i₀ j₀ a₀ : Fin 2) :
    IsLatinSquare (latinSquareFinTwoWithCell i₀ j₀ a₀) := by
  constructor
  · intro i x y hxy
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      fin_cases i₀ <;> fin_cases j₀ <;> fin_cases a₀ <;>
      simp [latinSquareFinTwoWithCell] at hxy ⊢
  · intro j x y hxy
    fin_cases j <;> fin_cases x <;> fin_cases y <;>
      fin_cases i₀ <;> fin_cases j₀ <;> fin_cases a₀ <;>
      simp [latinSquareFinTwoWithCell] at hxy ⊢

private theorem latinSquareFinTwoWithCell_spec (i₀ j₀ a₀ : Fin 2) :
    latinSquareFinTwoWithCell i₀ j₀ a₀ i₀ j₀ = a₀ := by
  simp [latinSquareFinTwoWithCell]

theorem latin_square_completion_order_two
    (P : Fin 2 → Fin 2 → Option (Fin 2))
    (hfilled_le : (filledCells P).card ≤ 1) :
    ∃ L : Fin 2 → Fin 2 → Fin 2, Completes P L := by
  classical
  by_cases hfilled : ∃ i j a, P i j = some a
  · rcases hfilled with ⟨i₀, j₀, a₀, hcell₀⟩
    refine ⟨latinSquareFinTwoWithCell i₀ j₀ a₀, ?_⟩
    constructor
    · exact isLatinSquare_latinSquareFinTwoWithCell i₀ j₀ a₀
    · intro i j a hcell
      have hmem : (i, j) ∈ filledCells P := by
        simp [filledCells, hcell]
      have hmem₀ : (i₀, j₀) ∈ filledCells P := by
        simp [filledCells, hcell₀]
      have hp_eq : (i, j) = (i₀, j₀) :=
        (Finset.card_le_one_iff.mp hfilled_le) hmem hmem₀
      have hi : i = i₀ := congrArg Prod.fst hp_eq
      have hj : j = j₀ := congrArg Prod.snd hp_eq
      subst i
      subst j
      have ha : a = a₀ := by
        have hsome : some a = some a₀ := by
          rw [← hcell, hcell₀]
        exact Option.some.inj hsome
      subst a
      exact latinSquareFinTwoWithCell_spec i₀ j₀ a₀
  · refine ⟨latinSquareFinTwoWithCell 0 0 0, ?_⟩
    constructor
    · exact isLatinSquare_latinSquareFinTwoWithCell 0 0 0
    · intro i j a hcell
      exact False.elim (hfilled ⟨i, j, a, hcell⟩)







private theorem finThree_sub_eq_zero_iff_eq (x y : Fin 3) : x - y = 0 ↔ x = y := by
  fin_cases x <;> fin_cases y <;> decide

private theorem finThree_mul_sub (u x y : Fin 3) :
    u * (x - y) = u * x - u * y := by
  fin_cases u <;> fin_cases x <;> fin_cases y <;> decide

private theorem finThree_sub_add_sub (a b c d : Fin 3) :
    (a - b) + (c - d) = (a + c) - (b + d) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

private theorem finThree_add_sub_of_sub_eq {x y a b : Fin 3}
    (h : x - y = b - a) : x + (a - y) = b := by
  fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b <;> revert h <;> decide

private theorem exists_nonzero_mul_add_eq_finThree
    (di dj da : Fin 3) (hnot : di ≠ 0 ∨ dj ≠ 0)
    (hrow : di = 0 → da ≠ 0) (hcol : dj = 0 → da ≠ 0) :
    ∃ u v : Fin 3, u ≠ 0 ∧ v ≠ 0 ∧ u * di + v * dj = da := by
  fin_cases di <;> fin_cases dj <;> fin_cases da <;>
    simp at hnot hrow hcol ⊢ <;> decide

private theorem mul_left_cancel_finThree {u x y : Fin 3} (hu : u ≠ 0)
    (h : u * x = u * y) : x = y := by
  fin_cases u <;> simp at hu h ⊢
  all_goals fin_cases x <;> fin_cases y <;> simp at h ⊢



private theorem isLatinSquare_linearLatinFinThree {u v c : Fin 3}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    IsLatinSquare (linearLatinFinThree u v c) := by
  constructor
  · intro i x y hxy
    unfold linearLatinFinThree at hxy
    have h1 : u * i + v * x = u * i + v * y := add_right_cancel hxy
    have h2 : v * x = v * y := add_left_cancel h1
    exact mul_left_cancel_finThree hv h2
  · intro j x y hxy
    unfold linearLatinFinThree at hxy
    have h1 : u * x + v * j = u * y + v * j := add_right_cancel hxy
    have h2 : u * x = u * y := add_right_cancel h1
    exact mul_left_cancel_finThree hu h2

private theorem linearLatinFinThree_spec_left
    (u v i j a : Fin 3) :
    linearLatinFinThree u v (a - (u * i + v * j)) i j = a := by
  fin_cases u <;> fin_cases v <;> fin_cases i <;> fin_cases j <;> fin_cases a <;>
    decide

private theorem linearLatinFinThree_spec_right
    (u v i₁ j₁ a₁ i₂ j₂ a₂ : Fin 3)
    (h : u * (i₂ - i₁) + v * (j₂ - j₁) = a₂ - a₁) :
    linearLatinFinThree u v (a₁ - (u * i₁ + v * j₁)) i₂ j₂ = a₂ := by
  apply finThree_add_sub_of_sub_eq
  calc
    u * i₂ + v * j₂ - (u * i₁ + v * j₁)
        = (u * i₂ - u * i₁) + (v * j₂ - v * j₁) := by
            rw [finThree_sub_add_sub]
    _ = u * (i₂ - i₁) + v * (j₂ - j₁) := by
            rw [finThree_mul_sub, finThree_mul_sub]
    _ = a₂ - a₁ := h

private theorem latin_square_completion_order_three_two_cells
    (P : Fin 3 → Fin 3 → Option (Fin 3)) (hP : IsPartialLatin P)
    {i₁ j₁ a₁ i₂ j₂ a₂ : Fin 3}
    (hcell₁ : P i₁ j₁ = some a₁) (hcell₂ : P i₂ j₂ = some a₂)
    (hne : (i₁, j₁) ≠ (i₂, j₂))
    (hfilled_le : (filledCells P).card ≤ 2) :
    ∃ L : Fin 3 → Fin 3 → Fin 3, Completes P L := by
  classical
  have hnot : i₂ - i₁ ≠ 0 ∨ j₂ - j₁ ≠ 0 := by
    by_contra h
    push Not at h
    have hi₂ : i₂ = i₁ := (finThree_sub_eq_zero_iff_eq i₂ i₁).mp h.1
    have hj₂ : j₂ = j₁ := (finThree_sub_eq_zero_iff_eq j₂ j₁).mp h.2
    exact hne (Prod.ext hi₂.symm hj₂.symm)
  have hrow : i₂ - i₁ = 0 → a₂ - a₁ ≠ 0 := by
    intro hi hsym
    have hi₂ : i₂ = i₁ := (finThree_sub_eq_zero_iff_eq i₂ i₁).mp hi
    have ha₂ : a₂ = a₁ := (finThree_sub_eq_zero_iff_eq a₂ a₁).mp hsym
    have hcell₂' : P i₁ j₂ = some a₁ := by simpa [hi₂, ha₂] using hcell₂
    have hj : j₁ = j₂ := hP.1 i₁ j₁ j₂ a₁ hcell₁ hcell₂'
    exact hne (Prod.ext hi₂.symm hj)
  have hcol : j₂ - j₁ = 0 → a₂ - a₁ ≠ 0 := by
    intro hj hsym
    have hj₂ : j₂ = j₁ := (finThree_sub_eq_zero_iff_eq j₂ j₁).mp hj
    have ha₂ : a₂ = a₁ := (finThree_sub_eq_zero_iff_eq a₂ a₁).mp hsym
    have hcell₂' : P i₂ j₁ = some a₁ := by simpa [hj₂, ha₂] using hcell₂
    have hi : i₁ = i₂ := hP.2 i₁ i₂ j₁ a₁ hcell₁ hcell₂'
    exact hne (Prod.ext hi hj₂.symm)
  obtain ⟨u, v, hu, hv, hsolve⟩ :=
    exists_nonzero_mul_add_eq_finThree (i₂ - i₁) (j₂ - j₁) (a₂ - a₁) hnot hrow hcol
  let c : Fin 3 := a₁ - (u * i₁ + v * j₁)
  refine ⟨linearLatinFinThree u v c, ?_⟩
  constructor
  · exact isLatinSquare_linearLatinFinThree hu hv
  · intro i j a hcell
    let S := filledCells P
    have hmem : (i, j) ∈ S := by simp [S, filledCells, hcell]
    have hmem₁ : (i₁, j₁) ∈ S := by simp [S, filledCells, hcell₁]
    have hmem₂ : (i₂, j₂) ∈ S := by simp [S, filledCells, hcell₂]
    by_cases hp₁ : (i, j) = (i₁, j₁)
    · have hi : i = i₁ := congrArg Prod.fst hp₁
      have hj : j = j₁ := congrArg Prod.snd hp₁
      subst i
      subst j
      have ha : a = a₁ := by
        have hsome : some a = some a₁ := by rw [← hcell, hcell₁]
        exact Option.some.inj hsome
      subst a
      exact linearLatinFinThree_spec_left u v i₁ j₁ a₁
    · have hcard_erase : (S.erase (i₁, j₁)).card ≤ 1 := by
        have hcard : S.card ≤ 2 := hfilled_le
        rw [Finset.card_erase_of_mem hmem₁]
        omega
      have hmem_erase : (i, j) ∈ S.erase (i₁, j₁) := by simp [hmem, hp₁]
      have hmem₂_erase : (i₂, j₂) ∈ S.erase (i₁, j₁) := by simp [hmem₂, hne.symm]
      have hp₂ : (i, j) = (i₂, j₂) :=
        (Finset.card_le_one_iff.mp hcard_erase) hmem_erase hmem₂_erase
      have hi : i = i₂ := congrArg Prod.fst hp₂
      have hj : j = j₂ := congrArg Prod.snd hp₂
      subst i
      subst j
      have ha : a = a₂ := by
        have hsome : some a = some a₂ := by rw [← hcell, hcell₂]
        exact Option.some.inj hsome
      subst a
      exact linearLatinFinThree_spec_right u v i₁ j₁ a₁ i₂ j₂ a₂ hsolve

theorem latin_square_completion_order_three
    (P : Fin 3 → Fin 3 → Option (Fin 3))
    (hP : IsPartialLatin P) (hfilled_le : (filledCells P).card ≤ 2) :
    ∃ L : Fin 3 → Fin 3 → Fin 3, Completes P L := by
  classical
  by_cases hle_one : (filledCells P).card ≤ 1
  · exact latin_square_completion_card_le_one P hle_one
  · have hone_lt : 1 < (filledCells P).card := by omega
    obtain ⟨p₁, hp₁, p₂, hp₂, hpne⟩ := Finset.one_lt_card.mp hone_lt
    obtain ⟨a₁, hcell₁⟩ : ∃ a, P p₁.1 p₁.2 = some a := by
      have hs : (P p₁.1 p₁.2).isSome := by simpa [filledCells] using hp₁
      cases hopt : P p₁.1 p₁.2 with
      | none => simp [hopt] at hs
      | some a => exact ⟨a, rfl⟩
    obtain ⟨a₂, hcell₂⟩ : ∃ a, P p₂.1 p₂.2 = some a := by
      have hs : (P p₂.1 p₂.2).isSome := by simpa [filledCells] using hp₂
      cases hopt : P p₂.1 p₂.2 with
      | none => simp [hopt] at hs
      | some a => exact ⟨a, rfl⟩
    exact latin_square_completion_order_three_two_cells P hP hcell₁ hcell₂ hpne hfilled_le

theorem latin_square_completion_order_le_three (n : ℕ) (hn : n ≤ 3)
    (P : Fin n → Fin n → Option (Fin n))
    (hP : IsPartialLatin P) (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  interval_cases n
  · simpa using latin_square_completion_order_zero P
  · simpa using latin_square_completion_order_one P
  · simpa using latin_square_completion_order_two P hfilled_le
  · simpa using latin_square_completion_order_three P hP hfilled_le

theorem latin_square_completion_theorem_order_le_three (n : ℕ) (hn : n ≤ 3) :
    LatinSquareCompletionTheorem n := by
  intro P hP hfilled_le
  exact latin_square_completion_order_le_three n hn P hP hfilled_le

theorem evansExactCardinalityCase_of_completion {n : ℕ}
    (hcomplete : LatinSquareCompletionTheorem n) :
    EvansExactCardinalityCase n := by
  intro P hP hcard
  exact hcomplete P hP (by omega)



theorem evansExactCardinalityCase_le_three (n : ℕ) (hn : n ≤ 3) :
    EvansExactCardinalityCase n :=
  evansExactCardinalityCase_of_completion (latin_square_completion_theorem_order_le_three n hn)



theorem chapter33_order_le_three (n : ℕ) (hn : n ≤ 3) :
    LatinSquareCompletionTheorem n :=
  completion_from_exact_cardinality_case (evansExactCardinalityCase_le_three n hn)



































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

theorem exists_symbol_occursExactlyOnce_of_many_used {n : ℕ}
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

lemma fin_castSucc_ne_last {N : ℕ} (i : Fin N) :
    (Fin.castSucc i : Fin (N + 1)) ≠ Fin.last N := by
  intro h
  have hv : i.val = N := by
    simpa [Fin.castSucc, Fin.last] using congrArg Fin.val h
  exact (Nat.ne_of_lt i.isLt) hv











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

theorem exists_relabel_singleton_smetaniukTriangularNormalized {N : ℕ}
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





theorem reverseColumnsPartial_completion_iff {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) :
    (∃ L : Fin n → Fin n → Fin n, Completes (reverseColumnsPartial P) L) ↔
      ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  simpa [reverseColumnsPartial] using
    completion_exists_relabelPartial_iff (Equiv.refl (Fin n)) Fin.revPerm
      (Equiv.refl (Fin n)) P

theorem smetMainPartial_completable_of_smetBackPartial_completable {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N}
    (h : ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetBackPartial L₀) L) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetMainPartial L₀) L := by
  exact (reverseColumnsPartial_completion_iff (smetBackPartial L₀)).mpr h



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

lemma isPartialLatin_smetMainKeepLastShrink {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hP : IsPartialLatin P) : IsPartialLatin (smetMainKeepLastShrink P) := by
  constructor
  · intro i j₁ j₂ a h₁ h₂
    have h₁P := (smetMainKeepLastShrink_eq_some_iff P i j₁ a).mp h₁
    have h₂P := (smetMainKeepLastShrink_eq_some_iff P i j₂ a).mp h₂
    have hcols :
        Fin.rev (Fin.castSucc j₁) = Fin.rev (Fin.castSucc j₂) :=
      hP.1 (Fin.castSucc i) (Fin.rev (Fin.castSucc j₁))
        (Fin.rev (Fin.castSucc j₂)) (Fin.castSucc a) h₁P h₂P
    have hcast : Fin.castSucc j₁ = Fin.castSucc j₂ :=
      Fin.revPerm.injective hcols
    exact Fin.castSucc_inj.mp hcast
  · intro i₁ i₂ j a h₁ h₂
    have h₁P := (smetMainKeepLastShrink_eq_some_iff P i₁ j a).mp h₁
    have h₂P := (smetMainKeepLastShrink_eq_some_iff P i₂ j a).mp h₂
    have hrows :
        Fin.castSucc i₁ = Fin.castSucc i₂ :=
      hP.2 (Fin.castSucc i₁) (Fin.castSucc i₂) (Fin.rev (Fin.castSucc j))
        (Fin.castSucc a) h₁P h₂P
    exact Fin.castSucc_inj.mp hrows





lemma filledCells_smetMainKeepLastShrink_card_le_erase_newSymbol {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)))
    {d : Fin (N + 1)}
    (hmain : MainDiagonalNewSymbol P d (Fin.last N)) :
    (filledCells (smetMainKeepLastShrink P)).card ≤
      ((filledCells P).erase (d, d)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun ij : Fin N × Fin N =>
      ((Fin.castSucc ij.1 : Fin (N + 1)), Fin.rev (Fin.castSucc ij.2))) ?_ ?_
  · intro ij hij
    have hs : (smetMainKeepLastShrink P ij.1 ij.2).isSome := by
      simpa [filledCells] using hij
    cases hcell : smetMainKeepLastShrink P ij.1 ij.2 with
    | none =>
        simp [hcell] at hs
    | some a =>
        have hP := (smetMainKeepLastShrink_eq_some_iff P ij.1 ij.2 a).mp hcell
        have hne : ((Fin.castSucc ij.1 : Fin (N + 1)), Fin.rev (Fin.castSucc ij.2)) ≠
            (d, d) := by
          intro hp
          have hrow : (Fin.castSucc ij.1 : Fin (N + 1)) = d :=
            congrArg Prod.fst hp
          have hcol : Fin.rev (Fin.castSucc ij.2 : Fin (N + 1)) = d :=
            congrArg Prod.snd hp
          have hPdiag : P d d = some (Fin.castSucc a) := by
            simpa [hrow, hcol] using hP
          have hlast : Fin.castSucc a = Fin.last N := by
            exact Option.some.inj (by rw [← hPdiag, hmain.1])
          exact fin_castSucc_ne_last a hlast
        simp [filledCells, hP, hne]
  · intro x hx y hy hxy
    have hrow : x.1 = y.1 :=
      Fin.castSucc_inj.mp (congrArg Prod.fst hxy)
    have hcol_rev : Fin.rev (Fin.castSucc x.2) = Fin.rev (Fin.castSucc y.2) :=
      congrArg Prod.snd hxy
    have hcol_cast : Fin.castSucc x.2 = Fin.castSucc y.2 :=
      Fin.revPerm.injective hcol_rev
    exact Prod.ext hrow (Fin.castSucc_inj.mp hcol_cast)

theorem smetMainKeepLastShrink_step_of_mainDiagonalNewSymbol {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hP : IsPartialLatin P) {d : Fin (N + 1)}
    (hmain : MainDiagonalNewSymbol P d (Fin.last N))
    (hcard : (filledCells P).card ≤ N) :
    IsPartialLatin (smetMainKeepLastShrink P) ∧
      (filledCells (smetMainKeepLastShrink P)).card ≤ N - 1 := by
  constructor
  · exact isPartialLatin_smetMainKeepLastShrink hP
  · have hle := filledCells_smetMainKeepLastShrink_card_le_erase_newSymbol P hmain
    have hmem : (d, d) ∈ filledCells P := by
      simp [filledCells, hmain.1]
    have hpos : 0 < (filledCells P).card := Finset.card_pos.mpr ⟨(d, d), hmem⟩
    rw [Finset.card_erase_of_mem hmem] at hle
    omega

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

lemma smetMainPartial_extends_of_keepLastShrink_completion {N : ℕ}
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

theorem SmetBackDiagonalCompletableCore {N : ℕ} (hN : 3 ≤ N)
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

theorem smetMainPartial_completable_of_core
    {N : ℕ} (hN : 3 ≤ N) {L₀ : Fin N → Fin N → Fin N}
    (hL₀ : IsLatinSquare L₀) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetMainPartial L₀) L := by
  exact smetMainPartial_completable_of_smetBackPartial_completable
    (SmetBackDiagonalCompletableCore hN L₀ hL₀)





theorem smetaniuk_normalized_of_IH {N : ℕ} (hN : 3 ≤ N)
    (hIH : LatinSquareCompletionTheorem N)
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    {d : Fin (N + 1)}
    (hP : IsPartialLatin P)
    (hcard : (filledCells P).card ≤ N)
    (hnorm : SmetaniukTriangularNormalized P d (Fin.last N)) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1), Completes P L := by
  have hstep :=
    smetMainKeepLastShrink_step_of_mainDiagonalNewSymbol hP hnorm.1 hcard
  obtain ⟨L₀, hL₀⟩ := hIH (smetMainKeepLastShrink P) hstep.1 hstep.2
  obtain ⟨L, hL⟩ := smetMainPartial_completable_of_core hN hL₀.1
  exact ⟨L, completes_of_extendsPartial
    (smetMainPartial_extends_of_keepLastShrink_completion hL₀ hnorm) hL⟩





theorem latinSquareCompletion_step_of_ryser {N : ℕ} (hN : 3 ≤ N)
    (hIH : LatinSquareCompletionTheorem N)
    (hR : ryser_few_elements_completes (N + 1)) :
    LatinSquareCompletionTheorem (N + 1) := by
  classical
  intro P hP hcard
  by_cases hfew : 2 * (usedSymbols P).card ≤ N + 1
  · exact hR P hP hcard hfew
  · have hmany : N + 1 < 2 * (usedSymbols P).card :=
      Nat.lt_of_not_ge hfew
    obtain ⟨a, hone⟩ :=
      exists_symbol_occursExactlyOnce_of_many_used P hcard hmany
    have hcardN : (filledCells P).card ≤ N := by
      simpa using hcard
    obtain ⟨rowPerm, colPerm, symPerm, d, hnorm⟩ :=
      exists_relabel_singleton_smetaniukTriangularNormalized
        (P := P) (a := a) hcardN hone
    let P' : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)) :=
      relabelPartial rowPerm colPerm symPerm P
    have hP' : IsPartialLatin P' := by
      dsimp [P']
      exact isPartialLatin_relabelPartial rowPerm colPerm symPerm hP
    have hcard' : (filledCells P').card ≤ N := by
      dsimp [P']
      rw [filledCells_relabelPartial_card]
      exact hcardN
    obtain ⟨L', hL'⟩ :=
      smetaniuk_normalized_of_IH hN hIH hP' hcard' hnorm
    exact (completion_exists_relabelPartial_iff rowPerm colPerm symPerm P).mp
      ⟨L', hL'⟩

theorem chapter33_unconditional_of_ryser
    (hR : ∀ n : ℕ, ryser_few_elements_completes n) :
    ∀ n : ℕ, LatinSquareCompletionTheorem n := by
  intro n
  induction n with
  | zero =>
      exact chapter33_order_le_three 0 (by omega)
  | succ N ih =>
      by_cases hsmall : N + 1 ≤ 3
      · exact chapter33_order_le_three (N + 1) hsmall
      · have hN : 3 ≤ N := by omega
        exact latinSquareCompletion_step_of_ryser hN ih (hR (N + 1))



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

/-- Book Lemma 2: a sparse partial Latin square using at most `n / 2` symbols completes. -/
theorem lemma2_few_elements_completes (n : ℕ)
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

/-- The bridge: the Ryser-file theorem (book Lemma 2) discharges the
few-symbols hypothesis of the Smetaniuk-file induction.  `elementsUsed` and
`usedSymbols` are the same filter. -/
theorem ryser_hypothesis_holds (n : ℕ) : ryser_few_elements_completes n := by
  intro P hP hcard helem
  cases n with
  | zero =>
      exact ⟨fun i => i.elim0, ⟨fun i => i.elim0, fun j => j.elim0⟩,
        fun i => i.elim0⟩
  | succ m =>
      refine lemma2_few_elements_completes (m + 1) P hP (by omega) ?_
      have heq : elementsUsed P = usedSymbols P := by
        ext a
        simp [elementsUsed, usedSymbols]
      rw [heq]
      exact helem



end ProofsInTheBook.Chapter33

end


set_option autoImplicit true
open ProofsInTheBook.Chapter33

theorem solution :
    ∀ n : ℕ, LatinSquareCompletionTheorem n :=
  chapter33_unconditional_of_ryser ryser_hypothesis_holds
