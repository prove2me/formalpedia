-- Prove2me | solution 2 for lean_workbook_plus_62967
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:02.46+00:00
-- url     : https://prove2.me/submissions/733e24e3-5d0f-47d8-9e3f-eaf9306979ce

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (k : ℝ) : (k - 1 / 2) * (k + 2) * (k - 3) * (k + 1 / 3) = 0 ↔ k = 1 / 2 ∨ k = -2 ∨ k = 3 ∨ k = -1 / 3 := by
  constructor
  · intro h
    simp only [mul_eq_zero] at h
    rcases h with ((h|h)|h)|h
    · left; linarith
    · right; left; linarith
    · right; right; left; linarith
    · right; right; right; linarith
  · rintro (rfl|rfl|rfl|rfl) <;> norm_num
