-- Prove2me | solution 1 for lean_workbook_plus_39477
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:06.181206+00:00
-- url     : https://prove2.me/submissions/24f472c6-11cc-409e-a111-1504907c50b7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : x^2 - 4 * x * y - y^2 ≤ 2 * x^2 + 3 * y^2 := by
  intros
  have h : (0 : ℝ) ≤ (2 * x^2 + 3 * y^2) - (x^2 - 4 * x * y - y^2) := by
    calc
      0 ≤ (4 : ℝ) * ((y + ((1 / 2) * x)))^2 := by positivity
      _ = (2 * x^2 + 3 * y^2) - (x^2 - 4 * x * y - y^2) := by ring
  exact sub_nonneg.mp h
