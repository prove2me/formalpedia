-- Prove2me | solution 1 for BookSixth.pairwise_disjoint_open_neighbourhoods
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T22:33:02.710615+00:00
-- url     : https://prove2.me/submissions/ff69d6d4-2f5f-402a-bf27-dca48a1fbcfc

import Mathlib
import Definitions.Def_BookSixth

open scoped Topology

open Set
open BookSixth

/-- Pairwise disjoint compact sets have pairwise disjoint open neighbourhoods.

For each ordered pair of distinct indices, positive clearance lets us thicken
both components by half that clearance and still obtain *disjoint* open
neighbourhoods `A ⊇ S i` and `B ⊇ S j`.  Intersecting the `A`-side coming from
`sep i j` with the `B`-side coming from `sep j i` yields, for each `i`, an open
`U i ⊇ S i` such that the two halves of a single separation always land on
opposite sides, so `U i ∩ U j = ∅`. -/
theorem solution {n : ℕ} (S : Fin n → Set Space3) (hS : ∀ i, IsCompact (S i))
    (hD : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    ∃ U : Fin n → Set Space3, (∀ i, IsOpen (U i)) ∧ (∀ i, S i ⊆ U i) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) := by
  classical
  have sep : ∀ i j : Fin n, i ≠ j → ∃ A B : Set Space3,
      IsOpen A ∧ IsOpen B ∧ S i ⊆ A ∧ S j ⊆ B ∧ Disjoint A B := by
    intro i j hij
    have hSj : IsClosed (S j) := (hS j).isClosed
    have hsub : S i ⊆ (S j)ᶜ := Set.disjoint_left.mp (hD i j hij)
    obtain ⟨δ, hδ, hth⟩ :=
      IsCompact.exists_thickening_subset_open (hS i) hSj.isOpen_compl hsub
    have hhalf : (0 : ℝ) < δ / 2 := by linarith
    refine ⟨Metric.thickening (δ / 2) (S i), Metric.thickening (δ / 2) (S j),
      Metric.isOpen_thickening, Metric.isOpen_thickening, ?_, ?_, ?_⟩
    · intro x hx
      exact Metric.mem_thickening_iff.mpr ⟨x, hx, by simpa using hhalf⟩
    · intro x hx
      exact Metric.mem_thickening_iff.mpr ⟨x, hx, by simpa using hhalf⟩
    · rw [Set.disjoint_left]
      intro x hxA hxB
      obtain ⟨a, ha, hxa⟩ := Metric.mem_thickening_iff.mp hxA
      obtain ⟨b, hb, hxb⟩ := Metric.mem_thickening_iff.mp hxB
      have hbA : b ∈ Metric.thickening δ (S i) := by
        refine Metric.mem_thickening_iff.mpr ⟨a, ha, ?_⟩
        have e1 : dist a b ≤ dist a x + dist x b := dist_triangle a x b
        have hxa' : dist a x < δ / 2 := by
          rw [dist_comm]
          simpa [Real.dist_eq] using hxa
        have hxb' : dist x b < δ / 2 := by simpa [Real.dist_eq] using hxb
        rw [dist_comm b a]
        linarith [e1]
      exact hth hbA hb
  choose A B hAo hBo hSiA hSjB hAB using sep
  let U : Fin n → Set Space3 :=
    fun i => ⋂ (j : {j : Fin n // j ≠ i}),
      (A i j.1 (Ne.symm j.2) ∩ B j.1 i j.2)
  have hopen : ∀ i, IsOpen (U i) := by
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact (hAo i j.1 (Ne.symm j.2)).inter (hBo j.1 i j.2)
  have hsub : ∀ i, S i ⊆ U i := by
    intro i x hx
    refine mem_iInter.2 fun j : {j : Fin n // j ≠ i} => ?_
    exact ⟨hSiA i j.1 (Ne.symm j.2) hx, hSjB j.1 i j.2 hx⟩
  refine ⟨U, hopen, hsub, fun i j hij => ?_⟩
  refine Set.disjoint_left.2 fun x hxi hxj => ?_
  have hA : x ∈ A i j hij := by
    have h2 := mem_iInter.1
      (show x ∈ ⋂ (k : {k : Fin n // k ≠ i}),
        (A i k.1 (Ne.symm k.2) ∩ B k.1 i k.2) from hxi) ⟨j, Ne.symm hij⟩
    exact h2.1
  have hB : x ∈ B i j hij := by
    have h2 := mem_iInter.1
      (show x ∈ ⋂ (k : {k : Fin n // k ≠ j}),
        (A j k.1 (Ne.symm k.2) ∩ B k.1 j k.2) from hxj) ⟨i, hij⟩
    exact h2.2
  exact Set.disjoint_left.1 (hAB i j hij) hA hB
