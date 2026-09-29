-- Prove2me | solution 1 for mme_112_normalized_weight_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:33:19.771695+00:00
-- url     : https://prove2.me/submissions/914a590f-990c-4e39-8684-d65e05b5e6cf

import Theorems.Thm_mme_112_weight_rate_algebra

open MME MME.RegionRate

/-- A normalized 112 certificate bounds the actual copy and dimension rate.
Region and split-mass bounds control the loss independently of the cell. -/
theorem solution
    (D a b c k : ℕ) (hD : 0 < D) (ha : 2 * a ≤ D)
    (hb : b ≤ D) (hc : c ≤ 2 * D)
    (tau delta bound : ℝ) (hdelta : 0 ≤ delta)
    (hbound : bound ≤
      4 * (entropy ![(a : ℝ) / D, (a : ℝ) / D, 1 - 2 * ((a : ℝ) / D)] + 2 * Real.log 2) +
        24 * (1 - (a : ℝ) / D) * tau * Real.log 5) :
    ((2 * k : ℕ) : ℝ) * (D : ℝ) ^ 4 *
        (((b : ℝ) / D) * ((c : ℝ) / D) * bound / 2 - 4 * delta) ≤
      ((4 * (D * (k * (b * c * D))) : ℕ) : ℝ) *
        (Real.log 2 * (mme_modern_entropyBits
          ![(a : ℝ) / D, (a : ℝ) / D, 1 - 2 * ((a : ℝ) / D)] + 2) - delta) +
      ((6 * (4 * ((D - 2 * a) * (k * (b * c * D))) +
        2 * ((2 * a) * (k * (b * c * D)))) : ℕ) : ℝ) * tau * Real.log 5 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  let theta : ℝ := ((b : ℝ) / D) * ((c : ℝ) / D) / 2
  have htheta0 : 0 ≤ theta := by dsimp [theta]; positivity
  have htheta1 : theta ≤ 1 := by
    have hb' : (b : ℝ) / D ≤ 1 := (div_le_one hDR).2 (by exact_mod_cast hb)
    have hc' : (c : ℝ) / D ≤ 2 := (div_le_iff₀ hDR).2 (by exact_mod_cast hc)
    have hb0 : (0 : ℝ) ≤ (b : ℝ) / D := by positivity
    have hc0 : (0 : ℝ) ≤ (c : ℝ) / D := by positivity
    dsimp [theta]
    nlinarith
  rw [mme_112_weight_rate_algebra D a (k * (b * c * D)) hD ha]
  have hscale : ((D * (k * (b * c * D)) : ℕ) : ℝ) =
      ((2 * k : ℕ) : ℝ) * (D : ℝ) ^ 4 * theta := by
    dsimp [theta]
    push_cast
    field_simp
  rw [hscale]
  have hrate : theta * bound - 4 * delta ≤ theta *
      (4 * (entropy ![(a : ℝ) / D, (a : ℝ) / D, 1 - 2 * ((a : ℝ) / D)] +
        2 * Real.log 2 - delta) + 24 * (1 - (a : ℝ) / D) * tau * Real.log 5) := by
    have h := mul_le_mul_of_nonneg_left hbound htheta0
    nlinarith
  have h := mul_le_mul_of_nonneg_left hrate
    (show 0 ≤ ((2 * k : ℕ) : ℝ) * (D : ℝ) ^ 4 by positivity)
  convert h using 1 <;> dsimp [theta] <;> ring


#print axioms solution
