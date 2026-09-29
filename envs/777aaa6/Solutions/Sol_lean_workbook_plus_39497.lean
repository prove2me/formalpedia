-- Prove2me | solution 1 for lean_workbook_plus_39497
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:12.539828+00:00
-- url     : https://prove2.me/submissions/b78dbb39-02e9-45db-bc4a-2fb260875586

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) :
  0 ≤ ((Real.sqrt 3) * x - 1)^2 * (2 * x + Real.sqrt 3) := by
  intros
  have p2m_sqrt_nonneg_0 := Real.sqrt_nonneg (3)
  have p2m_sqrt_square_0 : (Real.sqrt (3))^2 = (3) := Real.sq_sqrt (by first | positivity | linarith | nlinarith [sq_nonneg x])
  first | nlinarith [sq_nonneg x] | ((repeat' apply And.intro) <;> nlinarith [sq_nonneg x])
