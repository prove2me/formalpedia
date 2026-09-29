-- Prove2me | solution 1 for lean_workbook_plus_41249
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:52.385185+00:00
-- url     : https://prove2.me/submissions/e1aef847-2cd5-4dbf-8e19-41048ae0f9b8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} :
  a^4 + b^4 + c^4 + 3 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) -
    2 * (b * c * (b^2 + c^2) + c * a * (c^2 + a^2) + a * b * (a^2 + b^2)) ≥ 0 := by
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
