-- Prove2me | solution 1 for lean_workbook_plus_24456
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:10:40.86887+00:00
-- url     : https://prove2.me/submissions/d77ad6a9-b71d-4e66-b3f8-c642f9a5dc27

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (n : ℝ)
  (h₀ : n ≠ 1)
  (h₁ : n ≠ -1) :
  n^2 / (n^2 - 1) = 1 + 1 / (2 * (n - 1)) - 1 / (2 * (n + 1)) := by
  have hd : n ^ 2 - 1 ≠ 0 := by
    intro hz
    have hp : (n - 1) * (n + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with hp | hp
    · apply h₀; linarith
    · apply h₁; linarith
  have hm : n - 1 ≠ 0 := sub_ne_zero.mpr h₀
  have hp : n + 1 ≠ 0 := by intro h; apply h₁; linarith
  field_simp [hd, hm, hp]
  <;> ring
