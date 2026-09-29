-- Prove2me | solution 1 for lean_workbook_plus_68292
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:11:43.16943+00:00
-- url     : https://prove2.me/submissions/99fd44b9-5669-4d18-a869-625ac3d177bf

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (a b c : ℝ) : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) ↔ (a-b)^2+(b-c)^2+(c-a)^2 ≥ 0 := by
  constructor <;> intro h <;> nlinarith
