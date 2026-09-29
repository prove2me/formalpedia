-- Prove2me | solution 1 for lean_workbook_plus_15715
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:57.060881+00:00
-- url     : https://prove2.me/submissions/5c4060f4-8c10-4fdf-9a4d-9d6ede75ece1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : x = 5)
  (h₁ : y + Real.sqrt (25 - y^2) = 7)
  (h₂ : 25 - y^2 = (7 - y)^2) :
  2 * y^2 - 14 * y + 24 = 0 := by
  (intros; linarith)
