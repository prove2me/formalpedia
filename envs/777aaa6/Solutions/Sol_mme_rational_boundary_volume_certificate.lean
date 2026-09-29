-- Prove2me | solution 1 for mme_rational_boundary_volume_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:46.438608+00:00
-- url     : https://prove2.me/submissions/119194a5-5128-4ce2-8954-7ff3259979f9

import Theorems.Thm_mme_rational_mass_entropy_log_bounds
import Theorems.Thm_mme_CW5_base_log_bounds

open scoped BigOperators
open MME.RegionRate

/-- Rational mass and logarithm certificates bound a boundary cell's entropy
and free-letter volume together, at any nonnegative physical scale. -/
theorem solution
    {W : Type*} [Fintype W] (x : W → ℚ) (hx : ∀ w, 0 ≤ x w)
    (ones : W → ℕ) (lower upper : W → ℚ)
    (hlog : ∀ w, 0 < x w / ∑ v, x v →
      (lower w : ℝ) ≤ Real.log ((x w / ∑ v, x v : ℚ) : ℝ) ∧
        Real.log ((x w / ∑ v, x v : ℚ) : ℝ) ≤ (upper w : ℝ))
    (bound : ℚ)
    (hcert : bound ≤ (∑ w, x w) * (-(∑ w, (x w / ∑ v, x v) * upper w)) +
      (∑ w, x w * (ones w : ℚ)) * (1609437912434 / 1000000000000))
    (scale : ℝ) (hscale : 0 ≤ scale) :
    scale * (bound : ℝ) ≤ massEntropy (fun w ↦ scale * (x w : ℝ)) +
      (∑ w, (scale * (x w : ℝ)) * (ones w : ℝ)) * Real.log 5 := by
  have he := (mme_rational_mass_entropy_log_bounds x hx lower upper hlog).1
  have h5 := (mme_CW5_base_log_bounds 1).1
  norm_num only [Matrix.cons_val_one, Matrix.cons_val_zero, Rat.cast_div,
    Rat.cast_ofNat] at h5
  have ho : (0 : ℝ) ≤ ∑ w, (x w : ℝ) * (ones w : ℝ) := by
    apply Finset.sum_nonneg
    intro w hw
    exact mul_nonneg (by exact_mod_cast hx w) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left h5 ho
  have hc := (Rat.cast_le (K := ℝ)).2 hcert
  push_cast at he hc
  have hb : (bound : ℝ) ≤ massEntropy (fun w ↦ (x w : ℝ)) +
      (∑ w, (x w : ℝ) * (ones w : ℝ)) * Real.log 5 := by linarith
  have h := mul_le_mul_of_nonneg_left hb hscale
  rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := W)).1]
  simp only [mul_assoc, ← Finset.mul_sum]
  nlinarith [h]


#print axioms solution
