-- Prove2me | solution 1 for lean_workbook_plus_38256
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:24.195649+00:00
-- url     : https://prove2.me/submissions/566bc437-38ec-401d-9366-d157eae39a23

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (a b : ℝ)
  (h₀ : x = a - b)
  (h₁ : x = a - 1)
  (h₂ : x = b - 1)
  (h₃ : 2 * x^2 = (a - b)^2 + (a - 1)^2 + (b - 1)^2) :
  x = 0 := by
  (intros; simp_all)
