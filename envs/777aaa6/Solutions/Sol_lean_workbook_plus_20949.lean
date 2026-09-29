-- Prove2me | solution 1 for lean_workbook_plus_20949
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:11:08.902922+00:00
-- url     : https://prove2.me/submissions/bded7475-9f93-405e-95fe-0292ff1421c0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a b c : ℝ, 4 * (a + b + c) ^ 6 ≥ 27 * (a * b + b * c + c * a) * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) ^ 2 := by
  intro a b c
  have hf : 0 ≤ 4*(a+b+c)^2-3*(a*b+b*c+c*a) := by
    nlinarith [sq_nonneg (a+b+c), sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg (c-a)]
  have hp := mul_nonneg (sq_nonneg ((a+b+c)^2-3*(a*b+b*c+c*a))) hf
  nlinarith only [hp]
