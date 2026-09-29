-- Prove2me | solution 1 for lean_workbook_plus_30549
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:05.366323+00:00
-- url     : https://prove2.me/submissions/ec05874b-efaf-4bb9-8e6b-53b8f20fd056

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Real.sqrt (a / (a + b)) > a / (a + b) := by
  have ht : 0 < a/(a+b) := div_pos ha (add_pos ha hb)
  have ht1 : a/(a+b) < 1 := (div_lt_one (add_pos ha hb)).2 (by linarith)
  have hs := Real.sq_sqrt (le_of_lt ht)
  have hn := Real.sqrt_nonneg (a/(a+b))
  nlinarith [mul_pos ht (show 0 < 1-a/(a+b) by linarith)]
