-- Prove2me | solution 1 for lean_workbook_plus_48641
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:21.258288+00:00
-- url     : https://prove2.me/submissions/ecf5689f-7b44-436c-9401-10d15e238a58

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ ((2 * Real.sqrt 2 * (2:ℝ)^(1/7)) > 3) := by
  intro h
  norm_num at h
  have h2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith
