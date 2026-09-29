-- Prove2me | solution 1 for mme_released_interior_scaled_coarse_penalty_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:45:51.35214+00:00
-- url     : https://prove2.me/submissions/f46e7e8e-899a-4a76-bfda-41d8e92e1ac8

import Theorems.Thm_mme_regional_coarse_penalty_lower_bound
import Theorems.Thm_mme_released_interior_region_coarse_penalty
import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedInterior MME.MoreAsymmetryExactSeed

/-- The coarse-minus-penalty component of every released interior recipe
is at least two fifths of its parent mass, at every replication scale. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = []) (k : ℕ) :
    (2 / 5 : ℝ) * (k : ℝ) * (denominator : ℝ) ^ 4 ≤
      coarsePotential (fun r c => k * splitCount owner s r c) 0 -
        penaltyPotential (fun r => k * regionalSize owner s r)
          (fun r c => k * splitCount owner s r c) := by
  classical
  have hdata := mme_released_interior_scaled_integer_profile_constraints_exact owner s hi 1
    (by decide)
  dsimp only at hdata
  simp only [one_mul] at hdata
  obtain ⟨a, ha, htotal, _⟩ := hdata
  have hm (r : Fin 6) : ∑ c : Split s, splitCount owner s r c = regionalSize owner s r := by
    have hc := (Finset.mem_filter.mp ha).2 r
    change ∀ c, RecursiveThinSplit.count (a r) c = splitCount owner s r c at hc
    have hsum := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin (1 * regionalSize owner s r))) Finset.univ (a r)
    simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ,
      Fintype.card_fin] at hsum
    change (∑ c, RecursiveThinSplit.count (a r) c) = 1 * regionalSize owner s r at hsum
    simpa only [hc, one_mul] using hsum
  have hmk (r : Fin 6) : ∑ c : Split s, k * splitCount owner s r c =
      k * regionalSize owner s r := by rw [← Finset.mul_sum, hm]
  have hbound := mme_regional_coarse_penalty_lower_bound
    (fun r => k * regionalSize owner s r) (fun r c => k * splitCount owner s r c)
    hmk (2 / 5) ?_
  · have ht : (∑ r : Fin 6, k * regionalSize owner s r : ℕ) = k * denominator ^ 4 := by
      rw [← Finset.mul_sum, htotal]
    rw [ht] at hbound
    simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hbound
  · intro r hn
    have hr : 0 < (seed owner s).region.getD r.val 0 := by
      have h := Nat.pos_of_mul_pos_left hn
      unfold regionalSize at h
      exact Nat.pos_of_mul_pos_right h
    have hnR : (0 : ℝ) < (k * regionalSize owner s r : ℕ) := by exact_mod_cast hn
    have hnorm (c : Split s) :
        ((k * splitCount owner s r c : ℕ) : ℝ) /
          ((k * regionalSize owner s r : ℕ) : ℝ) =
        (splitWeight owner s r c : ℝ) / 1000000000000 := by
      apply (div_eq_iff hnR.ne').2
      unfold splitCount regionalSize denominator
      push_cast
      ring
    simpa only [hnorm] using mme_released_interior_region_coarse_penalty owner s r hi hr


#print axioms solution
