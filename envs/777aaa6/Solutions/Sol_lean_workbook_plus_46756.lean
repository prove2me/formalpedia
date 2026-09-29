-- Prove2me | solution 1 for lean_workbook_plus_46756
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:34:52.97013+00:00
-- url     : https://prove2.me/submissions/055531a5-ced5-4d1a-92a2-09acd521b16d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) :
  8 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) * (a^2 + b^2 + c^2) ≤
  9 * (a^2 + b^2) * (a^2 + c^2) * (b^2 + c^2) := by
  intros
  nlinarith [sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c), sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2)]
