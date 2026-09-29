-- Prove2me | solution 1 for lean_workbook_plus_38754
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:31.894759+00:00
-- url     : https://prove2.me/submissions/55dc9ccf-ee42-4418-a802-cfd6258698b5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) : (2*a^8 + 2*b^6 + a^4 - b^3 - 2*a^2 - 2) ≥ (-11/4) := by
  have hfactor : 0 ≤ 2 * a ^ 4 + 2 * a ^ 2 + (5 : ℝ) / 2 := by positivity
  have h := mul_nonneg (sq_nonneg (a ^ 2 - (1 : ℝ) / 2)) hfactor
  nlinarith [h, sq_nonneg (b ^ 3 - (1 : ℝ) / 4)]
