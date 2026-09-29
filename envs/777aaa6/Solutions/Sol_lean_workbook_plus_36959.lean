-- Prove2me | solution 1 for lean_workbook_plus_36959
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:48.586219+00:00
-- url     : https://prove2.me/submissions/0f247672-9213-43eb-8042-933f8f58af85

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℤ) : Even (x^7 + x^5) := by
  simp [Int.even_add,Int.even_pow]
