-- Prove2me | solution 1 for lean_workbook_plus_41130
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:14.150978+00:00
-- url     : https://prove2.me/submissions/b5af613f-b008-49ab-a5f9-d6f9d405a6b0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) : Real.sqrt (n * (n + 2)) < n + 1 := by
  intros
  have p2m_sqrt_nonneg_0 := Real.sqrt_nonneg (n * (n + 2))
  have p2m_sqrt_square_0 : (Real.sqrt (n * (n + 2)))^2 = (n * (n + 2)) := Real.sq_sqrt (by first | positivity | linarith | nlinarith [])
  first | nlinarith [] | (repeat constructor <;> nlinarith [])
