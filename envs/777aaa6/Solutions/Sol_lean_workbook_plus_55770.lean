-- Prove2me | solution 1 for lean_workbook_plus_55770
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:48:22.674077+00:00
-- url     : https://prove2.me/submissions/d9e02b77-9207-41af-852d-b8139d1b129c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) :
  1 / a^2 + 1 / b^2 + 1 / c^2 ≥ 1 / (a * b) + 1 / (b * c) + 1 / (c * a) := by
  simp only [one_div, mul_inv_rev, ← inv_pow]
  nlinarith [sq_nonneg (a⁻¹-b⁻¹), sq_nonneg (b⁻¹-c⁻¹), sq_nonneg (c⁻¹-a⁻¹)]
