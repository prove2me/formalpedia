-- Prove2me | solution 2 for lean_workbook_plus_29400
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:35.072482+00:00
-- url     : https://prove2.me/submissions/7834fd57-3941-4c18-ac0b-3888daf23753

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :  ∀ x y z : ℝ, x ^ 4 + y ^ 4 + z ^ 4 + 3 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) ≥ 2 * (x ^ 3 * (y + z) + y ^ 3 * (x + z) + z ^ 3 * (x + y)) := by
  intro x y z
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
