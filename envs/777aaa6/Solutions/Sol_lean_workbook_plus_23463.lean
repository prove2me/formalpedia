-- Prove2me | solution 1 for lean_workbook_plus_23463
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:55.475281+00:00
-- url     : https://prove2.me/submissions/a752c7f6-07a8-497e-9a44-2ddeb9ffe8d0

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (q : ℝ) : 1 ≤ |q| + |q + 1| := by
  have h := abs_sub_le (q+1) 0 q
  simpa [abs_neg,add_comm] using h
