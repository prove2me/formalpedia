-- Prove2me | solution 1 for lean_workbook_plus_41824
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:41:20.736119+00:00
-- url     : https://prove2.me/submissions/e9072b0d-1db9-4220-abbf-355ceb61e55f

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ)
  (h₀ : 1 ≤ a) :
  a^4 + a ≥ a^3 + 1 := by
  have h1 : 0 ≤ a - 1 := by linarith
  have h3 : 0 ≤ a ^ 3 + 1 := by positivity
  nlinarith [mul_nonneg h1 h3]
