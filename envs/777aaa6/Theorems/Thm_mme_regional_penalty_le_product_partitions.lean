-- Prove2me | Theorems.Thm_mme_regional_penalty_le_product_partitions
-- name    : mme_regional_penalty_le_product_partitions
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:07:52.688744+00:00
-- url     : https://prove2.me/theorems/7afec379-e251-45d4-b1f1-e788dd4fde3f
-- title:
--   Exact product partitions bound a joint regional penalty
-- statement:
--   For positive integer profile masses and exact joint histograms, summing the product-partition bounds gives an upper bound on the regional entropy penalty. This bound can be used before taking the minimum of the three aggregate directional rates. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_entropy_penalty_le_product_partition
import Definitions.Def_mme_regional_split_entropy_data
open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

theorem mme_regional_penalty_le_product_partitions
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
          entropy (fun c => (m r c : ℝ) / n r)) := by sorry
