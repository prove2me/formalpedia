-- Prove2me | solution 1 for lean_workbook_plus_38318
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:09.9858+00:00
-- url     : https://prove2.me/submissions/89fc4e30-cc6d-4ad0-989e-5e06ed9ea35c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y m n : ℤ) (h : 2017 ∣ y^2*m^2 - x^2*n^2) : 2017 ∣ (y*m - x*n)*(y*m + x*n) := by
  convert h using 1 <;> ring
