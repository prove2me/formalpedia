-- Prove2me | solution 1 for lean_workbook_plus_71340
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:03.434403+00:00
-- url     : https://prove2.me/submissions/3f979309-327f-44a1-999e-0ede0a820e4e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : y = 1) (h₂ : z = 1) : (x - 1) ^ 2 * x ^ 4 ≥ 0 := by
  (intros; positivity)
