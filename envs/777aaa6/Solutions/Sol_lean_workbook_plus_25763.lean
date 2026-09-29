-- Prove2me | solution 1 for lean_workbook_plus_25763
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:57.823475+00:00
-- url     : https://prove2.me/submissions/88440365-663f-4b1c-83fa-6c0bca50c054

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {x y z : ℝ} : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
