-- Prove2me | solution 1 for lean_workbook_plus_24414
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:56.818716+00:00
-- url     : https://prove2.me/submissions/a9c34641-97c4-42a9-ab83-04060205b223

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 + 4 * (x * y * z) ^ 2 ≥ 2 * (y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3 + x ^ 3 * y ^ 3) := by
  intros
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3), sq_nonneg (x^2 - z^2), sq_nonneg (x^3 - z^3), sq_nonneg (y^2 - z^2), sq_nonneg (y^3 - z^3)]
