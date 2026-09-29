-- Prove2me | solution 1 for lean_workbook_plus_44052
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:26.910821+00:00
-- url     : https://prove2.me/submissions/92ff0fa6-9a98-41a5-9f4d-bb36d785a64c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (1 / 2) * y ^ 6 + (1 / 2) * x ^ 2 * y ^ 2 ≥ x * y ^ 4 := by
  intros
  have h : (0 : ℝ) ≤ ((1 / 2) * y ^ 6 + (1 / 2) * x ^ 2 * y ^ 2) - (x * y ^ 4) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((y ^ 3) + ((-1) * x * y)))^2 := by positivity
      _ = ((1 / 2) * y ^ 6 + (1 / 2) * x ^ 2 * y ^ 2) - (x * y ^ 4) := by ring
  exact sub_nonneg.mp h
