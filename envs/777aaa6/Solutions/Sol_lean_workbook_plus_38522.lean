-- Prove2me | solution 1 for lean_workbook_plus_38522
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:38.288999+00:00
-- url     : https://prove2.me/submissions/85e78c1d-066b-4e41-955c-b87718def020

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : √((x ^ 2 + x * y + y ^ 2) / 3) ≥ (x + y) / 2 := by
  intros
  have p2m_sqrt_nonneg_0 := Real.sqrt_nonneg ((x ^ 2 + x * y + y ^ 2) / 3)
  have p2m_sqrt_square_0 : (Real.sqrt ((x ^ 2 + x * y + y ^ 2) / 3))^2 = ((x ^ 2 + x * y + y ^ 2) / 3) := Real.sq_sqrt (by first | positivity | linarith | nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)])
  first | nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)] | (repeat constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)])
