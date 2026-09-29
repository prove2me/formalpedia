-- Prove2me | solution 1 for lean_workbook_plus_46460
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:19:52.064768+00:00
-- url     : https://prove2.me/submissions/dac8e1b8-57fd-4422-9ef8-efdfa5a0d73c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a^2 + (-2*c + 3*b)*a + b^2 + c^2 - b*c ≥ 0 := by
  intro a b c
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
