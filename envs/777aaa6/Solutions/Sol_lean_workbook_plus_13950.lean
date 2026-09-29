-- Prove2me | solution 1 for lean_workbook_plus_13950
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:09.221254+00:00
-- url     : https://prove2.me/submissions/c99c163f-245d-4f66-9490-75e24d531244

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {x y : ℝ} : x ^ 2 + y ^ 2 ≥ 2 * x * y := by
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
