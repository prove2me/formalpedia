-- Prove2me | solution 1 for lean_workbook_plus_34269
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:58.882082+00:00
-- url     : https://prove2.me/submissions/ff8ce26e-7496-4476-bdef-25b05ba4581c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ c → (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
  intro a b c
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
