-- Prove2me | Theorems.Thm_mme_rational_product_dual_penalty_certificate
-- name    : mme_rational_product_dual_penalty_certificate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:32:45.162987+00:00
-- url     : https://prove2.me/theorems/4a5030a5-376e-46a2-873b-ba1939734088
-- title:
--   Certified logarithms bound product-dual entropy penalties
-- statement:
--   Positive normalized rational coordinate weights and certified logarithm bounds give a rational upper bound for the maximum-entropy penalty. Zero distribution atoms are allowed. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_entropy_penalty_le_product_dual
open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

theorem mme_rational_product_dual_penalty_certificate
    {half : ℕ} {parent : Fin 3 → ℕ}
    (alpha : Split half parent → ℚ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (weights : Fin 3 → Fin (half + 1) → ℚ)
    (hpos : ∀ i j, 0 < weights i j)
    (hmass : ∑ c : Split half parent, ∏ i, weights i (c.val i) ≤ 1)
    (weightLower : Fin 3 → Fin (half + 1) → ℚ)
    (alphaUpper : Split half parent → ℚ)
    (hwlog : ∀ i j, (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ))
    (halog : ∀ c, 0 < alpha c → Real.log (alpha c : ℝ) ≤ (alphaUpper c : ℝ))
    (bound : ℚ) :
    let m := fun i j => ∑ c : {c : Split half parent // c.val i = j}, alpha c.val;
    -(∑ i, ∑ j, m i j * weightLower i j) + ∑ c, alpha c * alphaUpper c ≤ bound →
      Real.log 2 * entropyPenalty (fun c => (alpha c : ℝ)) ≤ (bound : ℝ) := by sorry
