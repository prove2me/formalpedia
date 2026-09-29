-- Prove2me | solution 1 for lean_workbook_plus_39996
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:11:06.466623+00:00
-- url     : https://prove2.me/submissions/4ea58e29-816b-4044-bc6a-19786bf9f158

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) :
  1 / 2 * (x^4 * y^4 - x^4 * y^2 * z^2 + y^4 * z^4 - y^4 * z^2 * x^2 + z^4 * x^4 - z^4 * x^2 * y^2) ≥ 0 := by
  nlinarith only [sq_nonneg (x^2*y^2-y^2*z^2), sq_nonneg (y^2*z^2-z^2*x^2), sq_nonneg (z^2*x^2-x^2*y^2)]
