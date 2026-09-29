-- Prove2me | solution 1 for lean_workbook_plus_32528
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:35.2056+00:00
-- url     : https://prove2.me/submissions/e4242901-011d-401d-9ea0-7457c82a0737

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :  Real.sqrt ((a^2 + b^2) / 2) ≥ (a + b) / 2 := by
  intros
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
