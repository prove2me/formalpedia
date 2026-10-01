-- Prove2me | solution 1 for Real.Angle.coe_ne_coe_of_abs_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:07:21.111686+00:00
-- url     : https://prove2.me/submissions/64ebfa27-4c42-4c66-8167-d8427e66386f

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution {x y : ℝ} (hne : x ≠ y) (h : |x - y| < 2 * Real.pi) :
    ((x : ℝ) : Real.Angle) ≠ ((y : ℝ) : Real.Angle) := by
  intro he
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at he
  obtain ⟨k, hk⟩ := he
  have hpi := Real.pi_pos
  rw [abs_lt] at h
  rcases lt_trichotomy k 0 with hk0 | rfl | hk0
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    nlinarith [h.1]
  · simp only [Int.cast_zero, mul_zero] at hk
    exact hne (by linarith)
  · have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
    nlinarith [h.2]
