-- Prove2me | Theorems.Thm_mme_rational_entropy_log_bounds
-- name    : mme_rational_entropy_log_bounds
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:42:17.879999+00:00
-- url     : https://prove2.me/theorems/55f619f2-df10-4489-9ff1-88875ed4ccc1
-- title:
--   Rational logarithm enclosures bound entropy
-- statement:
--   Certified atom logarithms give sharp rational entropy intervals without a normalization hypothesis. Zero atoms require no logarithm certificate. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_entropy_dyadic_bounds
open scoped BigOperators
open MME.RegionRate

theorem mme_rational_entropy_log_bounds
    {W : Type*} [Fintype W] (p : W → ℚ) (hp : ∀ w, 0 ≤ p w)
    (lower upper : W → ℚ)
    (hlog : ∀ w, 0 < p w →
      (lower w : ℝ) ≤ Real.log (p w : ℝ) ∧
        Real.log (p w : ℝ) ≤ (upper w : ℝ)) :
    ((-(∑ w, p w * upper w) : ℚ) : ℝ) ≤ entropy (fun w => (p w : ℝ)) ∧
      entropy (fun w => (p w : ℝ)) ≤ ((-(∑ w, p w * lower w) : ℚ) : ℝ) := by sorry
