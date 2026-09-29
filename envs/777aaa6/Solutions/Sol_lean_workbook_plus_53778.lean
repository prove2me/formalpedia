-- Prove2me | solution 1 for lean_workbook_plus_53778
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:22.636461+00:00
-- url     : https://prove2.me/submissions/9719f41b-4dc3-48b3-89e3-29a68f0eec6e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ b c a : ℝ, (b - c + a) * (b + c - a) ≤ b^2 := by
  intro b c a
  intros
  nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg a, sq_nonneg (b - c), sq_nonneg (b - a), sq_nonneg (c - a)]
