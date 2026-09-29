-- Prove2me | solution 1 for lean_workbook_plus_25250
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:51.596508+00:00
-- url     : https://prove2.me/submissions/9371c90c-5568-47ea-89ed-d6451a7f0936

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  (intros; positivity)
