-- Prove2me | solution 1 for lean_workbook_plus_55516
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:46:00.895381+00:00
-- url     : https://prove2.me/submissions/1ee5b1de-0631-4a61-9b24-86c3631740e7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
    ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a →
    a * (2 * a^2 - b^2 - c^2) + b * (2 * b^2 - c^2 - a^2) + c * (2 * c^2 - a^2 - b^2) ≥ 0 := by
  intro a b c
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
