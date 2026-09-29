-- Prove2me | solution 1 for lean_workbook_plus_1263
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:58.668356+00:00
-- url     : https://prove2.me/submissions/fe7cfb0d-a324-4306-ba2b-23d0c44debdc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) :
  Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ≥ (x + y + z) / 3 := by
  intros
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
