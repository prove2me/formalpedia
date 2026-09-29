-- Prove2me | solution 1 for lean_workbook_plus_33273
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:36.32833+00:00
-- url     : https://prove2.me/submissions/1da3c7b9-e1a7-4ca5-b713-5cf432973a56

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ)
  (h₀ : 2 * (x^2 + 2) + 2 * y * (y + 2 * x) + y * (2 * x + y)^2 = 22 * y + 2 * (x^2 + 2) + 13 * y)
  (h₁ : y ≠ 0) :
  (2 * x + y + 7) * (2 * x + y - 5) = 0 := by
  intros
  grind
