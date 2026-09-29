-- Prove2me | solution 1 for lean_workbook_plus_59457
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:22.904672+00:00
-- url     : https://prove2.me/submissions/1135e9f7-ebcd-478f-81f4-8f35c9fc9871

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution :
  ((Real.sqrt 2 / 2)^3 * (Real.sqrt 2 / 2)^3) / ((1 + (Real.sqrt 2 / 2)^6) * (1 + (Real.sqrt 2 / 2)^6)) = 8 / 81 := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have ht : (Real.sqrt 2/2)^2 = 1/2 := by nlinarith
  have h6 : (Real.sqrt 2/2)^6 = 1/8 := by
    calc
      _ = ((Real.sqrt 2/2)^2)^3 := by ring
      _ = 1/8 := by rw [ht]; norm_num
  rw [show (Real.sqrt 2/2)^3*(Real.sqrt 2/2)^3 = (Real.sqrt 2/2)^6 by ring,h6]
  norm_num
