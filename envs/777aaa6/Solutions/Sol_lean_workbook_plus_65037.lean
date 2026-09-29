-- Prove2me | solution 1 for lean_workbook_plus_65037
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:55.725711+00:00
-- url     : https://prove2.me/submissions/20dd41aa-a1c7-4fde-a11c-540a217014de

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x + y = 28)
  (h₂ : 0.25 * x = 0.1 * y) :
  x = 8 := by
  (intros; linarith)
