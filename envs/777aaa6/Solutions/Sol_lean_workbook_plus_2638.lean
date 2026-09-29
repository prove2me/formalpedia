-- Prove2me | solution 1 for lean_workbook_plus_2638
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:42.876773+00:00
-- url     : https://prove2.me/submissions/a4d720ef-588d-4e51-8bb0-0de8b8399a4d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℚ) (h₁ : a = 19/9) (h₂ : b = 13/9) (h₃ : c = 4/3) : a + b + c = 19/9 + 13/9 + 4/3 := by
  (intros; simp_all)
