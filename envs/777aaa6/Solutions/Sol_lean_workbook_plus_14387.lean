-- Prove2me | solution 1 for lean_workbook_plus_14387
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:34.681704+00:00
-- url     : https://prove2.me/submissions/9652f03a-4edf-4498-aa48-266169051d86

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y u v : ℝ)
  (h₀ : u = x + y)
  (h₁ : v = x * y)
  (h₂ : u^3 - 2 * u * v = 8 * u^2 - 8 * v + 8) :
  u^3 - 2 * u * v = 8 * u^2 - 8 * v + 8 := by
  (intros; simp_all)
