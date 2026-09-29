-- Prove2me | solution 1 for lean_workbook_plus_70446
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:01.226963+00:00
-- url     : https://prove2.me/submissions/91d8a60f-756c-420e-a4fc-a8a2d66230d4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (c d : ℝ) : (2 * (c - 1) ^ 2 + (1 / 2) * (2 * Real.sqrt (d ^ 2 + 2 * d) - 1) ^ 2) ≥ 0 := by
  (intros; positivity)
