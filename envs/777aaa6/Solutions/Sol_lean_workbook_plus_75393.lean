-- Prove2me | solution 1 for lean_workbook_plus_75393
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:09:25.567741+00:00
-- url     : https://prove2.me/submissions/3d05ed41-4b97-43c2-a360-5aafe8871922

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ x y : ℝ,
    (x^2 + y^2) * (x^2 + y^2 - 2 * x)^2 = (x^2 - y^2)^2) := by
  intro h
  have hbad := h 2 0
  norm_num at hbad
  change (0 : ℝ) = (16 : ℝ) at hbad
  exact (by norm_num : (0 : ℝ) ≠ 16) hbad
