-- Prove2me | solution 1 for lean_workbook_plus_62716
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:33.997088+00:00
-- url     : https://prove2.me/submissions/e6287869-654e-486e-a8da-afde5f15c1bb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (m : ℕ) :
  ((m + 1)^2 - m^2 + 1) = 2 * (m + 1) := by
  have h : (m+1)^2 = m^2+2*m+1 := by ring
  omega
