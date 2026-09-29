-- Prove2me | solution 1 for mme_rational_scaled_mass_entropy_sum_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:04:57.060667+00:00
-- url     : https://prove2.me/submissions/de1fa453-d688-4c86-9f13-44f2f3882366

import Theorems.Thm_mme_rational_mass_entropy_log_bounds

open scoped BigOperators
open MME.RegionRate

/-- Rational logarithm intervals certify sums of homogeneous entropies at a
common physical scale. Zero rows and zero atoms need no logarithm bound. -/
theorem solution
    {A W : Type*} [Fintype A] [Fintype W]
    (x : A → W → ℚ) (hx : ∀ a w, 0 ≤ x a w)
    (lower upper : A → W → ℚ)
    (hlog : ∀ a w, 0 < x a w / ∑ v, x a v →
      (lower a w : ℝ) ≤ Real.log ((x a w / ∑ v, x a v : ℚ) : ℝ) ∧
        Real.log ((x a w / ∑ v, x a v : ℚ) : ℝ) ≤ (upper a w : ℝ))
    (scale : ℝ) (hscale : 0 ≤ scale) (bound : ℚ)
    (hcert : bound ≤ ∑ a, (∑ w, x a w) *
      (-(∑ w, (x a w / ∑ v, x a v) * upper a w))) :
    scale * (bound : ℝ) ≤
      ∑ a, massEntropy (fun w => scale * (x a w : ℝ)) := by
  have hl := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    (mme_rational_mass_entropy_log_bounds (x a) (hx a)
      (lower a) (upper a) (hlog a)).1)
  have hc := (Rat.cast_le (K := ℝ)).2 hcert
  push_cast at hl hc
  simp_rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := W)).1]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hc.trans hl) hscale


#print axioms solution
