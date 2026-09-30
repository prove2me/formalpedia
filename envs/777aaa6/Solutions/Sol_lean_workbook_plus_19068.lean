-- Prove2me | solution 1 for lean_workbook_plus_19068
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:10.254832+00:00
-- url     : https://prove2.me/submissions/66df058d-ff19-4431-9b67-6bc9b5b1e807

import Mathlib.Analysis.Complex.Basic

theorem solution {m n y z : ℝ} (hm : 0 < m) (hn : 0 < n) (hy : 0 < y) (hz : 0 < z) :
  (m * y + n * z) / (m + n) ≥ (m + n) / (m / y + n / z) := by
  have hyz : 0 < m / y + n / z := by positivity
  have hmn : 0 < m + n := by positivity
  rw [ge_iff_le, div_le_div_iff₀ hyz hmn]
  have key : (m + n) * (m + n) * (y * z) ≤ (m * y + n * z) * (m * z + n * y) := by
    nlinarith [mul_nonneg (mul_pos hm hn).le (sq_nonneg (y - z))]
  have e : (m * y + n * z) * (m / y + n / z) = (m * y + n * z) * (m * z + n * y) / (y * z) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  linarith
