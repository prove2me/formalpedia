-- Prove2me | solution 1 for lean_workbook_plus_8052
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:36.007557+00:00
-- url     : https://prove2.me/submissions/1f18b38b-1e84-4af9-8419-51a82404f56b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a + b = 7) (h₂ : 2 * a - b = 17) : a - b = 9 := by
  (intros; linarith)
