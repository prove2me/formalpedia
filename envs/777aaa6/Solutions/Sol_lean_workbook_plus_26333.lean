-- Prove2me | solution 1 for lean_workbook_plus_26333
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:18.362564+00:00
-- url     : https://prove2.me/submissions/d80c41d4-3f9e-4f52-8863-f7ea0e480cef

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} : (a * b + b * c + c * a) ^ 2 ≥ 3 * a * b * c * (a + b + c) := by
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
