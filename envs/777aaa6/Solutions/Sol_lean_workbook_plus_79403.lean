-- Prove2me | solution 1 for lean_workbook_plus_79403
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:35:49.498654+00:00
-- url     : https://prove2.me/submissions/1fd83780-066a-440c-b27f-2016784de2f9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ (∀ x y z : ℝ,
    x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 1 →
    x^2 * (x+y) * (x+z) + y^2 * (y+x) * (y+z) + z^2 * (z+x) * (z+y) ≥
      1 + (x+y)^2 + (x+z)^2 + (y+z)^2) := by
  intro h
  have hbad := h (1/3) (1/3) (1/3) (by norm_num)
  norm_num at hbad
