-- Prove2me | solution 1 for lean_workbook_plus_41350
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:53.13165+00:00
-- url     : https://prove2.me/submissions/6b4f116b-2b05-4e21-be4e-6966d1da3882

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, a * b * (a - c) * (c - b) + b * c * (b - a) * (a - c) + c * a * (c - b) * (b - a) ≤ 0 := by
  intro a b c
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
