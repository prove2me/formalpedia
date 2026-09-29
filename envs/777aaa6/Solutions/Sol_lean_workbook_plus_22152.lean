-- Prove2me | solution 1 for lean_workbook_plus_22152
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:35.50949+00:00
-- url     : https://prove2.me/submissions/a3f8f5fa-b501-4cc8-9e34-e7ad5845414f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : a ^ 6 + b ^ 6 + c ^ 6 ≥ 3 * a ^ 2 * b ^ 2 * c ^ 2 := by
  intros
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - b^3), sq_nonneg (a^2 - c^2), sq_nonneg (a^3 - c^3), sq_nonneg (b^2 - c^2), sq_nonneg (b^3 - c^3)]
