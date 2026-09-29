-- Prove2me | solution 1 for lean_workbook_plus_17311
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:49:52.120907+00:00
-- url     : https://prove2.me/submissions/be9ad67d-a794-4d70-92ab-0a44a15e0724

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (b c : ℝ) : Real.sqrt ((b^2 + c^2) / 2) ≥ (b + c) / 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ (b^2+c^2)/2 by positivity)
  have hn := Real.sqrt_nonneg ((b^2+c^2)/2)
  nlinarith [sq_nonneg (b-c)]
