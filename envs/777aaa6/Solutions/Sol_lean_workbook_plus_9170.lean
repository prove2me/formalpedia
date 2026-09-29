-- Prove2me | solution 1 for lean_workbook_plus_9170
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:13.411049+00:00
-- url     : https://prove2.me/submissions/c7b00a35-0564-44f7-a070-18512c4ea5c8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b c : ℝ) : 2 * Real.sqrt (3 * (a ^ 6 + b ^ 6 + c ^ 6)) ≥ 2 * (a ^ 3 + b ^ 3 + c ^ 3) := by
  have hs : (a^3+b^3+c^3)^2 ≤ 3*(a^6+b^6+c^6) := by
    nlinarith [sq_nonneg (a^3-b^3),sq_nonneg (b^3-c^3),sq_nonneg (c^3-a^3)]
  linarith [Real.le_sqrt_of_sq_le hs]
