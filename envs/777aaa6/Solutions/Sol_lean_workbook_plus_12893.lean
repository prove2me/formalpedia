-- Prove2me | solution 1 for lean_workbook_plus_12893
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:42.627513+00:00
-- url     : https://prove2.me/submissions/bda213f9-ebde-4d4b-92f3-7fee2e069a41

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c d : ℝ, 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≥ 2 * (a * b + a * c + a * d + b * c + b * d + c * d) := by
  intro a b c d
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
