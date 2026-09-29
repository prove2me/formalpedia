-- Prove2me | solution 1 for lean_workbook_plus_67993
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:29.119392+00:00
-- url     : https://prove2.me/submissions/7ed57164-600c-4025-a62d-0e494e90bf55

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {x : ℤ} (h : x ≡ 1 [ZMOD 4]) : x^2 ≡ 1 [ZMOD 4] := by
  simpa using h.pow 2
