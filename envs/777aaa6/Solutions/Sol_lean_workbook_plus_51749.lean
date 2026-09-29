-- Prove2me | solution 1 for lean_workbook_plus_51749
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:54.642135+00:00
-- url     : https://prove2.me/submissions/bd811a87-408f-4994-96a3-93349441651a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x^4 + y^4) * (x^2 + y^2) ≥ 2 * x^3 * y^3 := by
  intros
  have h : (0 : ℝ) ≤ ((x^4 + y^4) * (x^2 + y^2)) - (2 * x^3 * y^3) := by
    calc
      0 ≤ ((3 / 104) : ℝ) * (((y ^ 3) + (2 * x * (y ^ 2))))^2 + ((3 / 104) : ℝ) * (((y ^ 3) + ((-2) * x * (y ^ 2))))^2 + ((9 / 52) : ℝ) * (((y ^ 3) + (2 * y * (x ^ 2))))^2 + ((9 / 13) : ℝ) * (((y ^ 3) + ((-1) * (x ^ 3))))^2 + ((1 / 13) : ℝ) * (((y ^ 3) + ((-2) * (x ^ 3))))^2 + ((1 / 13) : ℝ) * (((x * (y ^ 2)) + ((-2) * y * (x ^ 2))))^2 := by positivity
      _ = ((x^4 + y^4) * (x^2 + y^2)) - (2 * x^3 * y^3) := by ring
  exact sub_nonneg.mp h
