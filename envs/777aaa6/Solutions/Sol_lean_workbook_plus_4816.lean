-- Prove2me | solution 1 for lean_workbook_plus_4816
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:30:41.520498+00:00
-- url     : https://prove2.me/submissions/cb624432-e445-496c-9367-dbf9211b72c4

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution {a b : ℤ} (h : a % 8 = b % 8) : a^2 % 8 = b^2 % 8 := by
  simpa [Int.ModEq] using (show Int.ModEq 8 a b from h).pow 2
