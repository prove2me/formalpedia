-- Prove2me | solution 1 for lean_workbook_plus_31031
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:32.653793+00:00
-- url     : https://prove2.me/submissions/a8dff72d-babd-48cf-aa0b-e0e23b40e719

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) : a + b - a * b ∈ Set.Icc 0 1 := by
  constructor
  · nlinarith [hb.1,mul_nonneg ha.1 (show 0 ≤ 1-b by linarith [hb.2])]
  · nlinarith [mul_nonneg (show 0 ≤ 1-a by linarith [ha.2]) (show 0 ≤ 1-b by linarith [hb.2])]
