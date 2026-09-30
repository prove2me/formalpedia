-- Prove2me | solution 1 for lean_workbook_plus_78681
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:41:03.895521+00:00
-- url     : https://prove2.me/submissions/2698c2d6-c645-46dc-9c41-b2393d69ad8e

import Mathlib

theorem general_remainder (t x y : ℝ) (ht : 0 < t) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    1/t + 1/(t+x+y) - (1/(t+x) + 1/(t+y)) =
      x*y*(2*t+x+y)/(t*(t+x)*(t+y)*(t+x+y)) := by
  have htx : 0 < t+x := by positivity
  have hty : 0 < t+y := by positivity
  have htxy : 0 < t+x+y := by positivity
  field_simp [ne_of_gt ht, ne_of_gt htx, ne_of_gt hty, ne_of_gt htxy]
  <;> ring

theorem general_bound (t x y : ℝ) (ht : 0 < t) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    1/(t+x) + 1/(t+y) ≤ 1/t + 1/(t+x+y) := by
  apply sub_nonneg.mp
  rw [general_remainder t x y ht hx hy]
  positivity

theorem strict_bound (t x y : ℝ) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    1/(t+x) + 1/(t+y) < 1/t + 1/(t+x+y) := by
  apply sub_pos.mp
  rw [general_remainder t x y ht (le_of_lt hx) (le_of_lt hy)]
  positivity

theorem solution : ∀ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x ≤ 1 ∧ y ≤ 1 →
    1/(1+x) + 1/(1+y) ≤ 1/(1+0) + 1/(1+x+y) := by
  intro x y h
  simpa only [add_zero, div_one] using general_bound 1 x y (by norm_num) h.1 h.2.1
