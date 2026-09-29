-- Prove2me | solution 1 for lean_workbook_plus_54606
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:21.900825+00:00
-- url     : https://prove2.me/submissions/08363335-0178-468d-90cb-0151fbbd078a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (g : ℝ → ℝ)
  (h₀ : g 9 = 9^4)
  (h₁ : g 3 = 3^4)
  (h₂ : g (-3) = (-3)^4) :
  g 9 + g 3 + g (-3) = 6723 := by
  (intros; linarith)
