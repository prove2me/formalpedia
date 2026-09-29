-- Prove2me | solution 1 for lean_workbook_plus_52734
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:09:32.153923+00:00
-- url     : https://prove2.me/submissions/f7808b08-17c0-43a2-9471-a3669f929164

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^3 ≥ a^3 + b^4) : a^3 + b^3 ≤ 2 := by
  nlinarith [mul_nonneg (sq_nonneg (a-1)) (by positivity : 0 ≤ 2*a+1), mul_nonneg (sq_nonneg (b-1)) (by positivity : 0 ≤ 3*b^2+2*b+1)]
