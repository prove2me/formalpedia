-- Prove2me | solution 1 for lean_workbook_plus_30135
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:30.495669+00:00
-- url     : https://prove2.me/submissions/600541e7-a6fd-4135-ab79-c1d940dc96aa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : a * (-1)^2 + b * (-1) + c = 12)
  (h₁ : a * 0^2 + b * 0 + c = 5)
  (h₂ : a * 2^2 + b * 2 + c = -3) :
  a + b + c = 0 := by
  (intros; linarith)
