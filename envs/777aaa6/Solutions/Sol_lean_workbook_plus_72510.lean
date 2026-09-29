-- Prove2me | solution 1 for lean_workbook_plus_72510
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:59.115333+00:00
-- url     : https://prove2.me/submissions/cc1b0ec9-66e6-4d4c-9150-44f12b23b260

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : (x ^ 4 + y ^ 4 + z ^ 4) ^ 2 ≥ (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 * y ^ 4 + y ^ 2 * z ^ 4 + z ^ 2 * x ^ 4) := by
  intros
  nlinarith [sq_nonneg (x * y), sq_nonneg (x * z), sq_nonneg (y * z), sq_nonneg (x^2 - y^2), sq_nonneg (x^2 - z^2), sq_nonneg (y^2 - z^2)]
