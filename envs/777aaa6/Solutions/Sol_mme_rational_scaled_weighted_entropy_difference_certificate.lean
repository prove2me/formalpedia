-- Prove2me | solution 1 for mme_rational_scaled_weighted_entropy_difference_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:23:35.730079+00:00
-- url     : https://prove2.me/submissions/d2cd04ea-5ee3-44ab-bdf6-ad5e96d27e5f

import Theorems.Thm_mme_rational_weighted_entropy_difference_log_certificate

open scoped BigOperators
open MME.RegionRate

/-- Rational entropy-difference certificates retain a common physical scale.
Parent entropies are weighted, while compatibility masses scale homogeneously. -/
theorem solution
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
    (scale : ℝ) (hscale : 0 ≤ scale) (bound : ℚ)
    (hcert : bound ≤ (∑ a, weight a * (-(∑ w, p a w * pUpper a w))) -
      ∑ c, (∑ v, x c v) * (-(∑ v, (x c v / ∑ u, x c u) * xLower c v))) :
    scale * (bound : ℝ) ≤
      (∑ a, (scale * (weight a : ℝ)) * entropy (fun w => (p a w : ℝ))) -
        ∑ c, massEntropy (fun v => scale * (x c v : ℝ)) := by
  have h := mme_rational_weighted_entropy_difference_log_certificate weight hweight
    p hp x hx pLower pUpper xLower xUpper hpLog hxLog bound hcert
  have hs := mul_le_mul_of_nonneg_left h hscale
  simp_rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := V)).1]
  simpa only [mul_sub, Finset.mul_sum, mul_assoc] using hs


#print axioms solution
