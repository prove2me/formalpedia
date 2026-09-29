-- Prove2me | solution 1 for lean_workbook_plus_32004
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:15:51.586197+00:00
-- url     : https://prove2.me/submissions/351f21f4-b854-49c6-860b-a3b78253eb36

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : (2 * Real.sqrt 3 - 2) > Real.sqrt 2 := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn2 := Real.sqrt_nonneg 2
  have hn3 := Real.sqrt_nonneg 3
  have hu : Real.sqrt 2 < 10/7 := by nlinarith
  have hl : 12/7 < Real.sqrt 3 := by nlinarith
  linarith
