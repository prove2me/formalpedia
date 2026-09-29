-- Prove2me | solution 1 for lean_workbook_plus_18049
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:19.073314+00:00
-- url     : https://prove2.me/submissions/4bc3d158-9412-4c23-932f-7df87cff3e66

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℤ) : Even (n^2 - n) := by
  simp [Int.even_sub, Int.even_pow]
