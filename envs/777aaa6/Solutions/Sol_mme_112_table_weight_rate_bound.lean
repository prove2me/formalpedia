-- Prove2me | solution 1 for mme_112_table_weight_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:54.322861+00:00
-- url     : https://prove2.me/submissions/57e76bea-50f5-4fc6-8824-28d0217aa529

import Theorems.Thm_mme_112_normalized_weight_rate_bound

open MME MME.RegionRate

/-- An already weighted 112 table bounds the actual child rate with the
same six-error allowance used for boundary children. -/
theorem solution
    (D a b c k : ℕ) (hD : 0 < D) (ha : 2 * a ≤ D)
    (hb : b ≤ D) (hc : c ≤ 2 * D)
    (tau delta bound : ℝ) (hdelta : 0 ≤ delta)
    (hbound : bound ≤ (((b : ℝ) / D) * ((c : ℝ) / D) / 2) *
      (4 * (entropy ![(a : ℝ) / D, (a : ℝ) / D, 1 - 2 * ((a : ℝ) / D)] + 2 * Real.log 2) +
        24 * (1 - (a : ℝ) / D) * tau * Real.log 5)) :
    ((2 * k : ℕ) : ℝ) * (D : ℝ) ^ 4 *
        (bound - 6 * delta) ≤
      ((4 * (D * (k * (b * c * D))) : ℕ) : ℝ) *
        (Real.log 2 * (mme_modern_entropyBits
          ![(a : ℝ) / D, (a : ℝ) / D, 1 - 2 * ((a : ℝ) / D)] + 2) - delta) +
      ((6 * (4 * ((D - 2 * a) * (k * (b * c * D))) +
        2 * ((2 * a) * (k * (b * c * D)))) : ℕ) : ℝ) * tau * Real.log 5 := by
  let rate : ℝ := 4 * (entropy ![(a : ℝ) / D, (a : ℝ) / D, 1 - 2 * ((a : ℝ) / D)] + 2 * Real.log 2) +
        24 * (1 - (a : ℝ) / D) * tau * Real.log 5
  have h := mme_112_normalized_weight_rate_bound D a b c k hD ha hb hc
    tau delta rate hdelta le_rfl
  have hbound' : bound ≤ (((b : ℝ) / D) * ((c : ℝ) / D) / 2) * rate := hbound
  have hq : bound - 6 * delta ≤
      ((b : ℝ) / D) * ((c : ℝ) / D) * rate / 2 - 4 * delta := by
    nlinarith
  exact (mul_le_mul_of_nonneg_left hq
    (show 0 ≤ ((2 * k : ℕ) : ℝ) * (D : ℝ) ^ 4 by positivity)).trans h


#print axioms solution
