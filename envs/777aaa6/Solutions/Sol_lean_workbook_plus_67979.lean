-- Prove2me | solution 1 for lean_workbook_plus_67979
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:36.859178+00:00
-- url     : https://prove2.me/submissions/6d61f25d-0205-4a00-9664-bfdb054e2660

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : √(7 + 4 * Real.sqrt 3) = 2 + Real.sqrt 3 := by
  intros
  have p2m_sqrt_nonneg_0 := Real.sqrt_nonneg (3)
  have p2m_sqrt_square_0 : (Real.sqrt (3))^2 = (3) := Real.sq_sqrt (by first | positivity | linarith | nlinarith [])
  have p2m_sqrt_nonneg_1 := Real.sqrt_nonneg (7 + 4 * Real.sqrt 3)
  have p2m_sqrt_square_1 : (Real.sqrt (7 + 4 * Real.sqrt 3))^2 = (7 + 4 * Real.sqrt 3) := Real.sq_sqrt (by first | positivity | linarith | nlinarith [])
  first | nlinarith [] | ((repeat' apply And.intro) <;> nlinarith [])
