-- Prove2me | solution 1 for lean_workbook_plus_19502
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:09.71584+00:00
-- url     : https://prove2.me/submissions/b6067b42-4312-4565-b867-707be637abac

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {a b c : ℝ} : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg (c-a)]
