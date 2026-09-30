-- Prove2me | solution 1 for lean_workbook_plus_58693
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:35:15.815542+00:00
-- url     : https://prove2.me/submissions/f4e0fe05-6cab-4e70-bf2c-15776d30b4f6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem comparison_gap (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x + 2 * y) / (y + 2 * x) - (y + 2 * x * y) / (x + 2 * x * y) =
      ((x - y) ^ 2 - 2 * y * ((x - y) * (x - 1))) /
        ((y + 2 * x) * (x + 2 * x * y)) := by
  have h1 : y + 2 * x ≠ 0 := ne_of_gt (by positivity)
  have h2 : x + 2 * x * y ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem comparison_refinement (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : (x - y) * (x - 1) ≤ 0) :
    (x - y) ^ 2 / ((y + 2 * x) * (x + 2 * x * y)) ≤
      (x + 2 * y) / (y + 2 * x) - (y + 2 * x * y) / (x + 2 * x * y) := by
  rw [comparison_gap x y hx hy]
  apply (div_le_div_iff_of_pos_right (by positivity)).2
  have hn := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * y by positivity) h
  linarith

theorem comparison_equality (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : (x - y) * (x - 1) ≤ 0) :
    (x + 2 * y) / (y + 2 * x) = (y + 2 * x * y) / (x + 2 * x * y) ↔
      x = y := by
  constructor
  · intro he
    have hr := comparison_refinement x y hx hy h
    rw [he, sub_self] at hr
    have hs := (div_le_iff₀ (show 0 < (y + 2 * x) * (x + 2 * x * y) by
      positivity)).mp hr
    nlinarith [sq_nonneg (x - y)]
  · rintro rfl
    apply sub_eq_zero.mp
    rw [comparison_gap x x hx hx]
    simp

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : 0 < x + y)
    (h : (x - y) * (x - 1) ≤ 0) :
    (x + 2 * y) / (y + 2 * x) ≥ (y + 2 * x * y) / (x + 2 * x * y) := by
  have hr := comparison_refinement x y hx hy h
  have hn : 0 ≤ (x - y) ^ 2 / ((y + 2 * x) * (x + 2 * x * y)) := by positivity
  linarith
