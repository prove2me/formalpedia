-- Prove2me | solution 1 for lean_workbook_plus_48394
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:00.382261+00:00
-- url     : https://prove2.me/submissions/03a9f3b2-eabf-4aa4-b65c-7b784c6dd0f8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z a b c : ℝ) (h₁ : a = x + y) (h₂ : b = y + z) (h₃ : c = z + x) : a + b + c = x + y + (y + z) + (z + x) := by
  (intros; simp_all)
