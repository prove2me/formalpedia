-- Prove2me | Theorems.Thm_mme_112_table_weight_rate_bound
-- name    : mme_112_table_weight_rate_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:57:22.488104+00:00
-- url     : https://prove2.me/theorems/2ecdd7b6-7f2f-46b2-b232-edd91b153f18
-- title:
--   Weighted 112 tables bound physical child rates
-- statement:
--   An already weighted 112 entropy and dimension certificate bounds the actual physical child rate with the same six-error allowance used for boundary children. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_112_normalized_weight_rate_bound
open MME MME.RegionRate

theorem mme_112_table_weight_rate_bound
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
        2 * ((2 * a) * (k * (b * c * D)))) : ℕ) : ℝ) * tau * Real.log 5 := by sorry
