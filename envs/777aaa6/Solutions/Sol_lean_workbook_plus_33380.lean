-- Prove2me | solution 1 for lean_workbook_plus_33380
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:41.458476+00:00
-- url     : https://prove2.me/submissions/4a9654d5-8c15-4784-91d4-5436db54d144

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  ∀ a b : ℝ, (a^8 + b^8 - a^6 * b^2 - b^6 * a^2) ≥ 0 := by
  intro a b
  intros
  nlinarith [sq_nonneg (a * b), sq_nonneg (a^2 - b^2)]
