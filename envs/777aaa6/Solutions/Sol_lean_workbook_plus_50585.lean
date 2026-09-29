-- Prove2me | solution 1 for lean_workbook_plus_50585
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:19.543622+00:00
-- url     : https://prove2.me/submissions/243c1b71-154d-4009-bd74-245c6c17428e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : Real.sqrt ((a^2 + b^2) * (a^2 + c^2)) ≥ a^2 + b * c := by
  intros
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
