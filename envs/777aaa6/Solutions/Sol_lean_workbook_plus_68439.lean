-- Prove2me | solution 1 for lean_workbook_plus_68439
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:16.536621+00:00
-- url     : https://prove2.me/submissions/a19bff52-384d-495e-9565-1e8afe98a192

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  intro x y z
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
