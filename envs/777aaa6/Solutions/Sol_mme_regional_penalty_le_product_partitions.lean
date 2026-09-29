-- Prove2me | solution 1 for mme_regional_penalty_le_product_partitions
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:32.421561+00:00
-- url     : https://prove2.me/submissions/11ac7a56-2682-4f78-af2b-87843e81e41f

import Theorems.Thm_mme_entropy_penalty_le_product_partition
import Definitions.Def_mme_regional_split_entropy_data

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

/-- Exact product partition functions bound the total penalty of a joint region.
The bound is summed before the regional directional minimum is taken. -/
theorem solution
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (hn : ∀ r, n r ≠ 0)
    (m : ∀ r, Split half (parent r) → ℕ)
    (hcounts : ∀ r, ∑ c, m r c = n r)
    (weights : Fin R → Fin 3 → Fin (half + 1) → ℝ)
    (hpos : ∀ r i j, 0 < weights r i j)
    (Z : Fin R → ℝ) (hZ : ∀ r, 0 < Z r)
    (hpartition : ∀ r, ∑ c : Split half (parent r),
      ∏ i, weights r i (c.val i) = Z r) :
    penaltyPotential n m ≤
      ∑ r, (n r : ℝ) *
        (Real.log (Z r) -
          (∑ i, ∑ j, mme_modern_marginal
            (fun c : Split half (parent r) => c.val i)
            (fun c => (m r c : ℝ) / n r) j * Real.log (weights r i j)) -
          entropy (fun c => (m r c : ℝ) / n r)) := by
  classical
  unfold penaltyPotential
  apply Finset.sum_le_sum
  intro r _
  have hnreal : (n r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hn r)
  have hprob : ∑ c : Split half (parent r), (m r c : ℝ) / n r = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hcounts,
      mul_inv_cancel₀ hnreal]
  have h := mme_entropy_penalty_le_product_partition
    (fun c => (m r c : ℝ) / n r)
    (fun c => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    hprob (weights r) (hpos r) (Z r) (hZ r) (hpartition r)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (n r))


#print axioms solution
