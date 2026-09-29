-- Prove2me | solution 1 for lean_workbook_plus_5441
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:01.591145+00:00
-- url     : https://prove2.me/submissions/9598e35e-adb7-4c40-bd9d-1f0da348a686

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (f : ℕ → ℕ) (h : f 0 = f 0 ^ 2) : f 0 = 0 ∨ f 0 = 1 := by
  by_cases h0 : f 0 = 0
  · exact Or.inl h0
  · right
    have hp : 1 ≤ f 0 := by omega
    have hu : f 0 ≤ 1 := by nlinarith
    omega
