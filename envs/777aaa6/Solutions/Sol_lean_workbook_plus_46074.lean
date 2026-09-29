-- Prove2me | solution 1 for lean_workbook_plus_46074
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:18.623733+00:00
-- url     : https://prove2.me/submissions/cc34ad8e-6289-476f-bdff-305de510b7f7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : (x - 3) ^ 2 + (y + 1) ^ 2 = 9) : x ^ 2 + y ^ 2 - 6 * x + 2 * y + 1 = 0 := by
  (intros; linarith)
