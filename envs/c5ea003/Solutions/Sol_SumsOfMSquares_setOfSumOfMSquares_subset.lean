-- Prove2me | solution 1 for SumsOfMSquares.setOfSumOfMSquares_subset
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:03:03.076381+00:00
-- url     : https://prove2.me/submissions/fefd30ce-a939-4cb6-8422-b343f6ba7e60

import Mathlib
import Definitions.Def_Novelty_SumsOfMSquaresSet
open SumsOfMSquares in
theorem solution {j m : ℕ} (hjm : j ≤ m) : setOfSumOfMSquares j ⊆ setOfSumOfMSquares m := by
  rintro n ⟨v, rfl⟩
  -- pad the representation with zeros
  let g : ℕ → ℕ := fun i => if h : i < j then v ⟨i, h⟩ else 0
  refine ⟨fun i => g i.val, ?_⟩
  have h1 : ∑ i : Fin j, (v i) ^ 2 = ∑ i : Fin j, (g i.val) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [g, i.isLt]
  show ∑ i : Fin m, (g i.val) ^ 2 = ∑ i : Fin j, (v i) ^ 2
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => g i ^ 2) m,
    Fin.sum_univ_eq_sum_range (fun i => g i ^ 2) j]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hjm)
  intro x _ hxj
  simp only [Finset.mem_range] at hxj
  simp [g, hxj]
