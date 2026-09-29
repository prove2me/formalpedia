-- Prove2me | solution 1 for lean_workbook_plus_5639
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:01:06.682317+00:00
-- url     : https://prove2.me/submissions/1802be8b-a502-44d0-9000-bd3fbd335e7b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℤ) (h : n ≡ 0 [ZMOD 3]) : n ^ 7 - n ≡ 0 [ZMOD 3] := by
  simpa using (h.pow 7).sub h
