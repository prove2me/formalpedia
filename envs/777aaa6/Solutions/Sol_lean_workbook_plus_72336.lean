-- Prove2me | solution 1 for lean_workbook_plus_72336
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:14.458471+00:00
-- url     : https://prove2.me/submissions/202eb5df-5759-4417-9cb5-56beed957d07

import Mathlib

set_option autoImplicit false

theorem solution (x n : ℕ) (hx : ∃ t, t ^ 2 = x) : ∃ t, t ^ 2 = x ^ n := by
  obtain ⟨t, rfl⟩ := hx
  refine ⟨t ^ n, ?_⟩
  simp only [← pow_mul, Nat.mul_comm]
