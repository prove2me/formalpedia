-- Prove2me | solution 1 for lean_workbook_plus_31926
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:01:51.541165+00:00
-- url     : https://prove2.me/submissions/1e571e7a-4a01-46ec-aa79-6ec0852170fe

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) :
  (2 * a * b - a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2 + 2 * c ^ 2) +
    (2 * b * c - b ^ 2 - c ^ 2) / (b ^ 2 + c ^ 2 + 2 * a ^ 2) +
      (2 * c * a - c ^ 2 - a ^ 2) / (c ^ 2 + a ^ 2 + 2 * b ^ 2) ≤
    0 := by
  have h (x y z : ℝ) : (2*x*y-x^2-y^2)/(x^2+y^2+2*z^2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (x-y)]) (by positivity)
  linarith [h a b c, h b c a, h c a b]
