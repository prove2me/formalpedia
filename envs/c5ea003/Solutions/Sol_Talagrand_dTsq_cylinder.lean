-- Prove2me | solution 1 for Talagrand.dTsq_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T02:01:14.745077+00:00
-- url     : https://prove2.me/submissions/caa45a4c-263d-4774-bc94-3d5ee44dacc0

import Mathlib
import Definitions.Def_Probability_TalagrandDefs
import Definitions.Def_Probability_TalagrandIsoperimetry
open Talagrand in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (B : Finset (Fin n))
    (c x : Fin n → α) :
    dTsq (cylinder B c) x = ((B.filter (fun i => x i ≠ c i)).card : ℝ) := by
  classical
  set D := B.filter (fun i => x i ≠ c i) with hD
  apply IsLeast.csInf_eq
  constructor
  · -- attained by the nearest point of the cylinder: `c` on `B`, `x` elsewhere
    let y : Fin n → α := fun i => if i ∈ B then c i else x i
    have hy : y ∈ cylinder B c := by
      simp only [cylinder, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      simp [y, hi]
    refine ⟨fun i => hamm (x i) (y i),
      ⟨1, fun _ => 1, fun _ => y, fun _ => zero_le_one, by simp, fun _ => hy, fun i => by simp⟩, ?_⟩
    unfold sqn
    have hsq : ∀ i, hamm (x i) (y i) ^ 2 = if i ∈ D then 1 else 0 := by
      intro i
      by_cases hi : i ∈ B <;> by_cases hx : x i = c i <;> simp [hamm, y, hD, hi, hx]
    rw [Finset.sum_congr rfl (fun i _ => hsq i), Finset.sum_ite_mem, Finset.univ_inter]
    simp
  · -- every representation has `v i = 1` on the coordinates where `x` leaves the cylinder
    rintro s ⟨v, ⟨k, w, y, hw0, hw1, hyA, hv⟩, rfl⟩
    have hvD : ∀ i ∈ D, v i = 1 := by
      intro i hi
      rw [hD, Finset.mem_filter] at hi
      rw [hv i]
      have hone : ∀ j, hamm (x i) (y j i) = 1 := by
        intro j
        have hyj := hyA j
        simp only [cylinder, Finset.mem_filter, Finset.mem_univ, true_and] at hyj
        rw [hyj i hi.1]
        simp [hamm, hi.2]
      simp [hone, hw1]
    unfold sqn
    calc (D.card : ℝ) = ∑ i ∈ D, v i ^ 2 := by
          rw [Finset.sum_congr rfl (fun i hi => by rw [hvD i hi])]
          simp
      _ ≤ ∑ i, v i ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
