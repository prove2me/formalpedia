-- Prove2me | solution 1 for lean_workbook_plus_12527
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:40.48758+00:00
-- url     : https://prove2.me/submissions/6503aa79-9850-41de-b7d7-101e8a9df021

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ x y z : ℝ, x^3 + 2 * x * y^2 + y^3 + 2 * y * z^2 + z^3 + 2 * z * x^2 ≥ 3 * (x^2 * y + y^2 * z + z^2 * x)) := by
  intro h
  linarith [h (-1) 0 0]
