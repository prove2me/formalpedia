-- Prove2me | solution 1 for mme_entropy_retention_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:18:51.323182+00:00
-- url     : https://prove2.me/submissions/c307d58f-a887-4287-a7d4-d0252232f355

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem solution (T Q A factor theta poly : ℝ) (hT : 0 ≤ T) (hQ : 0 < Q)
    (hfactor : 0 < factor) (hpoly : 0 < poly)
    (htarget : Real.exp A ≤ poly * T) (hscale : Q ≤ factor * Real.exp theta) :
    Real.exp (A - theta - 4 * Real.sqrt (Real.log factor + theta)) / (32 * poly * factor) ≤
      T * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) := by
  have hlog : Real.log Q ≤ Real.log factor + theta := by
    have h := Real.log_le_log hQ hscale
    simpa only [Real.log_mul (ne_of_gt hfactor) (Real.exp_ne_zero _),Real.log_exp] using h
  have he : Real.exp (-4 * Real.sqrt (Real.log factor + theta)) ≤
      Real.exp (-4 * Real.sqrt (Real.log Q)) :=
    Real.exp_le_exp.mpr (by have h := Real.sqrt_le_sqrt hlog; linarith)
  have ht : Real.exp A / poly ≤ T := (div_le_iff₀ hpoly).mpr (by nlinarith)
  calc
    _ = (Real.exp A / poly) * Real.exp (-4 * Real.sqrt (Real.log factor + theta)) /
        (32 * (factor * Real.exp theta)) := by
      rw [show A - theta - 4 * Real.sqrt (Real.log factor + theta) =
        A + (-4 * Real.sqrt (Real.log factor + theta)) - theta by ring,Real.exp_sub,Real.exp_add]
      field_simp
    _ ≤ T * Real.exp (-4 * Real.sqrt (Real.log factor + theta)) /
        (32 * (factor * Real.exp theta)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ ≤ T * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * (factor * Real.exp theta)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left he hT
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (mul_nonneg hT (Real.exp_pos _).le) (by positivity)
      exact mul_le_mul_of_nonneg_left hscale (by norm_num)
