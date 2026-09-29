-- Prove2me | solution 1 for lean_workbook_plus_40413
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:15.811714+00:00
-- url     : https://prove2.me/submissions/be0e0832-3cda-454a-b697-848f6b400ef3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : x^6 + x^5 + 6 * x^4 + 6 * x^3 + 7 * x^2 + 4 * x + 7 > 0 := by
  nlinarith only [sq_nonneg (x^3+x^2/2),sq_nonneg (x^2+x),sq_nonneg (x^2),sq_nonneg (2*x+1)]
