-- Prove2me | solution 1 for lean_workbook_plus_37513
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:31.349456+00:00
-- url     : https://prove2.me/submissions/f83686ce-e010-49db-9c33-6791ce34ddfb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z : ℝ, 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  intro x y z
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
