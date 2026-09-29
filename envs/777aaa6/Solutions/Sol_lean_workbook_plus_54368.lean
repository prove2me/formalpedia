-- Prove2me | solution 1 for lean_workbook_plus_54368
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:09:45.780641+00:00
-- url     : https://prove2.me/submissions/5b9e2674-49c8-45c9-8b6c-7a990a411714

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 + c^2 = 3 → a + b + c ≤ 3 := by
  rintro a b c ⟨ha, hb, hc, he⟩
  nlinarith [sq_nonneg (a-1), sq_nonneg (b-1), sq_nonneg (c-1)]
