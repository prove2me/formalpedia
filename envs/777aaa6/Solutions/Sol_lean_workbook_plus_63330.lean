-- Prove2me | solution 1 for lean_workbook_plus_63330
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:17:25.578843+00:00
-- url     : https://prove2.me/submissions/44c7f7b6-9492-4363-a80f-b0a2aae78f49

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v a b : ℝ) (h₁ : u > 0) (h₂ : v < -1) (h₃ : (a, b) = (u, -v)) : a = u ∧ b = -v := by
  (intros; simp_all)
