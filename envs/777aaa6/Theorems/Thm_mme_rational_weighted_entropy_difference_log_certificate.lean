-- Prove2me | Theorems.Thm_mme_rational_weighted_entropy_difference_log_certificate
-- name    : mme_rational_weighted_entropy_difference_log_certificate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:54:41.739786+00:00
-- url     : https://prove2.me/theorems/4888ef99-26f6-4f65-8e62-4f1fe8b013be
-- title:
--   Weighted entropy differences have rational logarithm certificates
-- statement:
--   Certified logarithm intervals give a rational lower bound for weighted parent entropies minus homogeneous compatibility entropies. Zero weights and zero masses are allowed. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_rational_mass_entropy_log_bounds
open scoped BigOperators
open MME.RegionRate

theorem mme_rational_weighted_entropy_difference_log_certificate
    {A W C V : Type*} [Fintype A] [Fintype W] [Fintype C] [Fintype V]
    (weight : A → ℚ) (hweight : ∀ a, 0 ≤ weight a)
    (p : A → W → ℚ) (hp : ∀ a w, 0 ≤ p a w)
    (x : C → V → ℚ) (hx : ∀ c v, 0 ≤ x c v)
    (pLower pUpper : A → W → ℚ) (xLower xUpper : C → V → ℚ)
    (hpLog : ∀ a w, 0 < p a w →
      (pLower a w : ℝ) ≤ Real.log (p a w : ℝ) ∧
        Real.log (p a w : ℝ) ≤ (pUpper a w : ℝ))
    (hxLog : ∀ c v, 0 < x c v / ∑ u, x c u →
      (xLower c v : ℝ) ≤ Real.log ((x c v / ∑ u, x c u : ℚ) : ℝ) ∧
        Real.log ((x c v / ∑ u, x c u : ℚ) : ℝ) ≤ (xUpper c v : ℝ))
    (bound : ℚ) :
    bound ≤ (∑ a, weight a * (-(∑ w, p a w * pUpper a w))) -
      ∑ c, (∑ v, x c v) * (-(∑ v, (x c v / ∑ u, x c u) * xLower c v)) →
    (bound : ℝ) ≤ (∑ a, (weight a : ℝ) * entropy (fun w => (p a w : ℝ))) -
      ∑ c, massEntropy (fun v => (x c v : ℝ)) := by sorry
