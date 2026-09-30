-- Prove2me | solution 2 for lean_workbook_plus_11657
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:39.700709+00:00
-- url     : https://prove2.me/submissions/46945825-2bc0-4818-ae2b-87d4bb7b1639

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (c : ℝ) : -3 * (c + 1) * (c - 13/3) ≥ 0 ↔ -1 ≤ c ∧ c ≤ 13/3 := by
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (c+1),sq_nonneg (c-13/3)]
  · rintro ⟨h1,h2⟩
    nlinarith [mul_nonneg (show 0 ≤ c+1 by linarith) (show 0 ≤ 13/3-c by linarith)]
