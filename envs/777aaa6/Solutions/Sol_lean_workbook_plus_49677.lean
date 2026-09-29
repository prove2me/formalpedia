-- Prove2me | solution 1 for lean_workbook_plus_49677
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:35:54.49248+00:00
-- url     : https://prove2.me/submissions/5ef60f85-cb76-456b-aebf-9ff2c2ad3e5c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : x = y)
  (h₁ : x^3 + y^3 = x - y) :
  x = 0 ∧ y = 0 := by
  (intros; simp_all)
