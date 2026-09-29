-- Prove2me | solution 1 for lean_workbook_plus_70358
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:30.908088+00:00
-- url     : https://prove2.me/submissions/b550c753-1ec5-4ecd-ae2e-4b5e8854df3a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : 125 * x + 50 * y = 3475)
  (h₁ : 20 * x + 50 * y = 1480) :
  x = 19 := by
  (intros; linarith)
