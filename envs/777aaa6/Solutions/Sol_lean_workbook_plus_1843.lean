-- Prove2me | solution 1 for lean_workbook_plus_1843
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:33.90615+00:00
-- url     : https://prove2.me/submissions/017decbb-12ad-4024-9138-42e6b09abbec

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ) (h : a = 10) : Real.sqrt (10 * 4 * 3 * 3) = 6 * Real.sqrt 10 := by
  intros
  have p2m_sqrt_nonneg_0 := Real.sqrt_nonneg (10)
  have p2m_sqrt_square_0 : (Real.sqrt (10))^2 = (10) := Real.sq_sqrt (by first | positivity | linarith | nlinarith [sq_nonneg a])
  have p2m_sqrt_nonneg_1 := Real.sqrt_nonneg (10 * 4 * 3 * 3)
  have p2m_sqrt_square_1 : (Real.sqrt (10 * 4 * 3 * 3))^2 = (10 * 4 * 3 * 3) := Real.sq_sqrt (by first | positivity | linarith | nlinarith [sq_nonneg a])
  first | nlinarith [sq_nonneg a] | ((repeat' apply And.intro) <;> nlinarith [sq_nonneg a])
