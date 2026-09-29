-- Prove2me | solution 1 for lean_workbook_plus_27740
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:35.037002+00:00
-- url     : https://prove2.me/submissions/27e1621c-6ef0-414f-bea5-2e7d8e231761

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : x = 15 / 2 * 1 / 2 * 9 / 2 * 5 / 2) : Real.sqrt x = 15 / 4 * Real.sqrt 3 := by
  intros
  have p2m_sqrt_nonneg_0 := Real.sqrt_nonneg (x)
  have p2m_sqrt_square_0 : (Real.sqrt (x))^2 = (x) := Real.sq_sqrt (by first | positivity | linarith | nlinarith [sq_nonneg x])
  have p2m_sqrt_nonneg_1 := Real.sqrt_nonneg (3)
  have p2m_sqrt_square_1 : (Real.sqrt (3))^2 = (3) := Real.sq_sqrt (by first | positivity | linarith | nlinarith [sq_nonneg x])
  first | nlinarith [sq_nonneg x] | (repeat constructor <;> nlinarith [sq_nonneg x])
