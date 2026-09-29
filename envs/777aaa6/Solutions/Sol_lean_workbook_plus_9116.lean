-- Prove2me | solution 1 for lean_workbook_plus_9116
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:09:57.00444+00:00
-- url     : https://prove2.me/submissions/f458f224-5a82-4ebb-84e4-bd93c5d63dea

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  ∀ x y z : ℝ, 6 * (x + y + z) ^ 2 ≥ 5 * (x ^ 2 + y ^ 2 + z ^ 2) + 13 * (x * y + y * z + z * x) := by
  intro x y z
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
