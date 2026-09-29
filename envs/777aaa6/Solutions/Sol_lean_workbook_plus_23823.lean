-- Prove2me | solution 1 for lean_workbook_plus_23823
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:38.360732+00:00
-- url     : https://prove2.me/submissions/ffab604c-598a-4717-bdfc-08f320a328b8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} : (2 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + a * b * c * (a + b + c) ≥ (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + a * c) := by
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
