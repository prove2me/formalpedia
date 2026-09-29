-- Prove2me | solution 1 for lean_workbook_plus_65026
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:34.889061+00:00
-- url     : https://prove2.me/submissions/aa36e807-5147-429d-b176-a6a72c1ac1ff

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, 2 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b + a * c + b * c ≥ 3 * (a * b + a * c + b * c) := by
  intro a b c
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
