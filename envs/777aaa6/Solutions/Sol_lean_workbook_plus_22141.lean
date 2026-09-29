-- Prove2me | solution 1 for lean_workbook_plus_22141
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:32.902136+00:00
-- url     : https://prove2.me/submissions/24fd3f40-8d78-4b5a-9fef-9e9823ad8bb8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (f : ℝ → ℝ) (hf : ∀ x, f x + f (1 - x) = 11) (hf' : ∀ x, f (1 + x) = 3 + f x) : ∀ x, f x + f (-x) = 8 := by
  intro x
  have h := hf x
  have h' := hf' (-x)
  have : 1 + -x = 1 - x := by ring
  rw [this] at h'
  linarith
