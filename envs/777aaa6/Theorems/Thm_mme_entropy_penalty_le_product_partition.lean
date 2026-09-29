-- Prove2me | Theorems.Thm_mme_entropy_penalty_le_product_partition
-- name    : mme_entropy_penalty_le_product_partition
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T09:15:41.753647+00:00
-- url     : https://prove2.me/theorems/180522f0-fa86-4627-bab8-04efa05068cd
-- title:
--   Product weights bound entropy with an exact partition function
-- statement:
--   Arbitrary positive coordinate weights give an entropy-penalty upper bound with the logarithm of their exact partition function. Normalizing one coordinate proves the result without approximate normalization assumptions. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_entropy_penalty_le_product_dual
open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

theorem mme_entropy_penalty_le_product_partition
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (weights : Fin 3 → Fin (half + 1) → ℝ)
    (hpos : ∀ i j, 0 < weights i j)
    (Z : ℝ) (hZ : 0 < Z)
    (hpartition : ∑ c : Split half parent, ∏ i, weights i (c.val i) = Z) :
    Real.log 2 * entropyPenalty alpha ≤
      Real.log Z -
        (∑ i, ∑ j, mme_modern_marginal (fun c : Split half parent => c.val i) alpha j *
          Real.log (weights i j)) - entropy alpha := by sorry
