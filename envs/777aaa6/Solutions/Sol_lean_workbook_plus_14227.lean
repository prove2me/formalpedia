-- Prove2me | solution 1 for lean_workbook_plus_14227
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:07:49.053187+00:00
-- url     : https://prove2.me/submissions/a860c094-434d-4d64-b224-800be4153c30

import Mathlib.Data.Real.Basic

theorem solution (f : ℝ → ℝ) (hf : ∀ x, f (x*f x) = x^2) :
    ∀ x, f x = 0 ↔ x = 0 := by
  have h0 : f 0 = 0 := by
    simpa only [zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hf 0
  intro x
  constructor
  · intro hx
    have hh := hf x
    rw [hx, mul_zero, h0] at hh
    exact sq_eq_zero_iff.mp hh.symm
  · rintro rfl
    exact h0
