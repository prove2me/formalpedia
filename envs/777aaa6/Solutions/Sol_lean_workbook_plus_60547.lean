-- Prove2me | solution 1 for lean_workbook_plus_60547
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:46:12.168997+00:00
-- url     : https://prove2.me/submissions/9869f738-9148-4f65-b0ea-bb12df6d071c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y s : ℝ)
  (h₀ : x + y = s)
  (h₁ : 2 * x + 2 * y + 12 = 2 * s + 12) :
  2 * x + 2 * y + 12 = 2 * (x + y) + 12 := by
  (intros; simp_all)
