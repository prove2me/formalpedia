-- Prove2me | solution 1 for lean_workbook_plus_74750
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:33.75208+00:00
-- url     : https://prove2.me/submissions/4a777fa4-2d06-4fc2-9d79-82a91a6275d6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (hab : a + b >= 1) : a^4 + b^4 >= 1/8 := by
  have h1 : 1 ≤ (a+b)^2 := by nlinarith
  have h2 : (a+b)^2 ≤ 2*(a^2+b^2) := by nlinarith [sq_nonneg (a-b)]
  nlinarith [sq_nonneg (a^2-b^2), sq_nonneg (a^2+b^2-1/2)]
