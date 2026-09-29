-- Prove2me | solution 1 for lean_workbook_plus_19450
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:04.109246+00:00
-- url     : https://prove2.me/submissions/3ab9f07b-8235-4507-818a-58e8abef9102

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution {a : ℤ} (h : a%2 = 1) : a ^ 2 ≡ 1 [ZMOD 2] := by
  have ha : a ≡ 1 [ZMOD 2] := h
  simpa using ha.pow 2
