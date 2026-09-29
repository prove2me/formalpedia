-- Prove2me | solution 1 for lean_workbook_plus_13857
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:12.463301+00:00
-- url     : https://prove2.me/submissions/fb26850a-1fac-42c1-8840-7020c8e6fce5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (h : ∀ x > 0, 3 * f x + 7 * f (2016 / x) = 2 * x) : f 8 = 87 := by
  intros
  grind
