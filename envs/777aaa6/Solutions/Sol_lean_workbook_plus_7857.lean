-- Prove2me | solution 1 for lean_workbook_plus_7857
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:36.072733+00:00
-- url     : https://prove2.me/submissions/972ec32f-03cf-4d5b-b2aa-f45dc5dc5740

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a → a * (b^2 + c^2 - a^2) + b * (c^2 + a^2 - b^2) + c * (a^2 + b^2 - c^2) ≤ 3 * a * b * c := by
  intro a b c
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
