-- Prove2me | solution 1 for lean_workbook_plus_55720
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:06:24.695586+00:00
-- url     : https://prove2.me/submissions/ae7b6b91-edd9-40dd-a0ff-5ef3c3edcf0e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem cleared_constraint (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 1 / (x + 2) + 2 / (y + 2) = 1 / 3) :
    (x + 2) * (y + 2) = 3 * (y + 2) + 6 * (x + 2) := by
  have hx2 : x + 2 ≠ 0 := ne_of_gt (by positivity)
  have hy2 : y + 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp at h
  nlinarith [h]

theorem exact_gap (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 1 / (x + 2) + 2 / (y + 2) = 1 / 3) :
    x + 2 * y - 21 = 6 * (x - y) ^ 2 / ((x + 2) * (y + 2)) := by
  have he := cleared_constraint x y hx hy h
  apply (eq_div_iff (ne_of_gt (by positivity : 0 < (x + 2) * (y + 2)))).mpr
  linear_combination (x + 2 * y + 6) * he

theorem parameter_classification (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (1 / (x + 2) + 2 / (y + 2) = 1 / 3) ↔
      ∃ t : ℝ, 0 < t ∧ x = 1 + t ∧ y = 4 + 18 / t := by
  constructor
  · intro h
    have he := cleared_constraint x y hx hy h
    have ht : 0 < x - 1 := by
      by_contra hn
      have hm := mul_nonpos_of_nonpos_of_nonneg (show x - 1 ≤ 0 by linarith) (le_of_lt hy)
      nlinarith [he]
    refine ⟨x - 1, ht, by ring, ?_⟩
    have hy' : y - 4 = 18 / (x - 1) := by
      apply (eq_div_iff (ne_of_gt ht)).mpr
      nlinarith [he]
    linarith
  · rintro ⟨t, ht, rfl, rfl⟩
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hx2 : 1 + t + 2 ≠ 0 := ne_of_gt (by positivity)
    have hy2 : 4 + 18 / t + 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring

theorem minimum_equality (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 1 / (x + 2) + 2 / (y + 2) = 1 / 3) :
    x + 2 * y = 21 ↔ x = 7 ∧ y = 7 := by
  constructor
  · intro he
    have hgap := exact_gap x y hx hy h
    have hn : (x + 2) * (y + 2) ≠ 0 := ne_of_gt (by positivity)
    have hz : 6 * (x - y) ^ 2 / ((x + 2) * (y + 2)) = 0 := by linarith
    have hz' := (div_eq_zero_iff.mp hz).resolve_right hn
    have hs : (x - y) ^ 2 = 0 := by nlinarith [hz']
    have hxy := sq_eq_zero_iff.mp hs
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ring

theorem minimum_attained : (0 : ℝ) < 7 ∧ 1 / (7 + 2) + 2 / (7 + 2) = (1 : ℝ) / 3 ∧
    (7 : ℝ) + 2 * 7 = 21 := by
  refine ⟨by positivity, ?_, ?_⟩ <;> ring

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 1 / (x + 2) + 2 / (y + 2) = 1 / 3) : x + 2 * y ≥ 21 := by
  have he := exact_gap x y hx hy h
  have hn : 0 ≤ 6 * (x - y) ^ 2 / ((x + 2) * (y + 2)) := by positivity
  linarith
