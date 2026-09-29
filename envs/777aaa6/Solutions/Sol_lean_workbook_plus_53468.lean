-- Prove2me | solution 1 for lean_workbook_plus_53468
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:23.436279+00:00
-- url     : https://prove2.me/submissions/d83e4cd1-a431-4bd2-bda2-a8cba13a87d9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - d^2)^2 + (d^2 - a^2)^2 ≥ 0 := by
  (intros; positivity)
