-- Prove2me | solution 1 for lean_workbook_plus_59462
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:12.088899+00:00
-- url     : https://prove2.me/submissions/b06f4341-33cf-4c4b-9490-1569ea51deb5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (hab : (a^2 + 1) * (b^2 + 1) = 4) : (a + 1) * (b - 1) ≥ -4 := by
  nlinarith [sq_nonneg (a*b+a),sq_nonneg (a*b-b),sq_nonneg (a*b+1),sq_nonneg (-a-b),sq_nonneg (1-a),sq_nonneg (b+1)]
