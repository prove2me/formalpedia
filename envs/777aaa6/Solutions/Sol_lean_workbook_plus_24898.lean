-- Prove2me | solution 1 for lean_workbook_plus_24898
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:37.904505+00:00
-- url     : https://prove2.me/submissions/661db919-d41a-4003-85b2-75a3731138b5

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x : ℝ) : 2 * x ^ 2 + 8 * x ≤ -6 ↔ -3 ≤ x ∧ x ≤ -1 := by
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨hl,hu⟩
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x+3 by linarith) (show x+1 ≤ 0 by linarith)]
