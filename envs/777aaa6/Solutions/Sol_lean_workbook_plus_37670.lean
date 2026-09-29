-- Prove2me | solution 1 for lean_workbook_plus_37670
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:35.070534+00:00
-- url     : https://prove2.me/submissions/ef782e3c-5413-4149-b473-6342e67672db

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 = 1 / 2 → a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a * b * c * (a + b + c) := by
  intro a b c
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
