-- Prove2me | solution 1 for lean_workbook_plus_6002
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:46:58.284918+00:00
-- url     : https://prove2.me/submissions/07e51f99-d712-4f21-8c22-066cde171fe4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z : ℝ, x^2 + y^2 + z^2 = 1 → x + y + z ≤ Real.sqrt 3 := by
  intro x y z
  intros
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
