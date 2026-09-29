-- Prove2me | solution 1 for mme_regional_coarse_penalty_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:04:40.544469+00:00
-- url     : https://prove2.me/submissions/78a4a63d-3744-48aa-89f4-3a33ebc4f3b2

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Definitions.Def_mme_regional_split_entropy_data

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

/-- Uniform bounds on normalized nonempty regions give a weighted bound
for the coarse potential minus the entropy-penalty potential. -/
theorem solution
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ c, m r c = n r) (b : ℝ)
    (hb : ∀ r, 0 < n r → b ≤
      entropy (mme_modern_marginal (fun c : Split half (parent r) => c.val 0)
        (fun c => (m r c : ℝ) / n r)) -
      Real.log 2 * entropyPenalty (fun c => (m r c : ℝ) / n r)) :
    b * (∑ r, n r : ℕ) ≤ coarsePotential m 0 - penaltyPotential n m := by
  classical
  have hmass (r : Fin R) : ∑ j, marginalCounts m 0 r j = n r := by
    rw [← hm r]
    exact Fintype.sum_fiberwise (fun c : Split half (parent r) => c.val 0) (m r)
  have hregion (r : Fin R) : b * (n r : ℝ) ≤
      massEntropy (fun j => (marginalCounts m 0 r j : ℝ)) -
        (n r : ℝ) * Real.log 2 * entropyPenalty (fun c => (m r c : ℝ) / n r) := by
    by_cases hz : n r = 0
    · have hj (j : Fin (half + 1)) : marginalCounts m 0 r j = 0 :=
        Finset.sum_eq_zero_iff.mp ((hmass r).trans hz) j (Finset.mem_univ j)
      simp [hz, hj, massEntropy, entropy]
    · have hn : 0 < n r := Nat.pos_of_ne_zero hz
      have hmassR : ∑ j, (marginalCounts m 0 r j : ℝ) = n r := by
        exact_mod_cast hmass r
      have hnR : (n r : ℝ) ≠ 0 := by exact_mod_cast hz
      have he := (mme_regional_mass_entropy_algebra (C := Unit)
        (W := Fin (half + 1))).2.1 (fun j => (marginalCounts m 0 r j : ℝ))
        (by rw [hmassR]; exact hnR)
      rw [hmassR] at he
      have heq : (fun j => (marginalCounts m 0 r j : ℝ) / n r) =
          mme_modern_marginal (fun c : Split half (parent r) => c.val 0)
            (fun c => (m r c : ℝ) / n r) := by
        funext j
        simp only [marginalCounts, Nat.cast_sum, mme_modern_marginal, Finset.sum_div]
      rw [he, heq]
      have h := mul_le_mul_of_nonneg_left (hb r hn) (Nat.cast_nonneg (n r) : (0 : ℝ) ≤ n r)
      nlinarith
  simpa only [coarsePotential, penaltyPotential, Nat.cast_sum, Finset.mul_sum,
    Finset.sum_sub_distrib] using Finset.sum_le_sum (fun r _ => hregion r)


#print axioms solution
