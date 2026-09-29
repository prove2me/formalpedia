-- Prove2me | solution 1 for lean_workbook_plus_9378
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:12:36.73445+00:00
-- url     : https://prove2.me/submissions/6286a134-7e65-4a43-b34e-ea51918d7d61

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) (h1 : x ^ 4 + y ^ 4 < 4) (h2 : x ^ 3 + y ^ 3 > 3) : x ^ 2 + y ^ 2 > 2 := by
  by_contra hn
  have hs : x^2+y^2 ≤ 2 := by linarith
  have hp := mul_nonneg (show 0 ≤ 4-(x^4+y^4) by linarith) (show 0 ≤ x^2+y^2 by positivity)
  have hq : (x^3+y^3)^2 ≤ 8 := by nlinarith [sq_nonneg (x^2*y-x*y^2)]
  nlinarith [sq_nonneg (x^3+y^3-3)]
