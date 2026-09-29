-- Prove2me | solution 1 for lean_workbook_plus_51044
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:24.892466+00:00
-- url     : https://prove2.me/submissions/079b32fd-9d32-4678-ad29-dda512822df7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x + 2*y = 1) (h₂ : y + 2*x = 2) : x + y = 1 := by
  (intros; linarith)
