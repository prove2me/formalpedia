-- Prove2me | solution 1 for lean_workbook_plus_81533
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:13:50.410616+00:00
-- url     : https://prove2.me/submissions/1aae7d2c-ef1d-4d01-b030-38f47d2d9c85

import Mathlib

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (Real.sqrt (a + b) / Real.sqrt 2) ≥ 2 / (1 / Real.sqrt a + 1 / Real.sqrt b) ↔
      Real.sqrt (a + b) * (1 / Real.sqrt a + 1 / Real.sqrt b) ≥ 2 * Real.sqrt 2 := by
  exact div_le_div_iff₀
    (add_pos (one_div_pos.mpr (Real.sqrt_pos.mpr ha))
      (one_div_pos.mpr (Real.sqrt_pos.mpr hb)))
    (Real.sqrt_pos.mpr (by norm_num))
