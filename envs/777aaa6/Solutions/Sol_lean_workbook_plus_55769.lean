-- Prove2me | solution 1 for lean_workbook_plus_55769
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:06:17.435706+00:00
-- url     : https://prove2.me/submissions/048edd22-84b8-4909-9fea-9c0e35c81965

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable def productGap (x y : ℝ) : ℝ :=
  (2 * x * y + x + y) * (x + y) + 1 - x * y - 3 * (2 * x * y + x + y) / 2

theorem small_sum_identity (x y : ℝ) :
    2 * productGap x y = (2 - (x + y)) * (x - y) ^ 2 +
      (x + y - 1) ^ 2 * (x + y + 2) := by unfold productGap; ring

theorem large_sum_identity (x y : ℝ) :
    productGap x y = 2 * x * y * (x + y - 2) + (x + y - 1) ^ 2 + (x + y) / 2 := by
  unfold productGap
  ring

theorem quantitative_small_sum (x y : ℝ) (hs : x + y ≤ 2) :
    (x + y - 1) ^ 2 * (x + y + 2) / 2 ≤ productGap x y := by
  have hp := mul_nonneg (show 0 ≤ 2 - (x + y) by linarith) (sq_nonneg (x - y))
  nlinarith [small_sum_identity x y]

theorem quantitative_large_sum (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : 2 ≤ x + y) :
    (x + y) / 2 ≤ productGap x y := by
  have hp : 0 ≤ 2 * x * y * (x + y - 2) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [large_sum_identity x y, sq_nonneg (x + y - 1)]

theorem nonnegative_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ productGap x y := by
  rcases le_total (x + y) 2 with hs | hs
  · have h := quantitative_small_sum x y hs
    have hp : 0 ≤ (x + y - 1) ^ 2 * (x + y + 2) / 2 := by positivity
    linarith
  · have h := quantitative_large_sum x y hx hy hs
    linarith

theorem full_equality (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    productGap x y = 0 ↔ x = 1 / 2 ∧ y = 1 / 2 := by
  constructor
  · intro he
    have hs : x + y ≤ 2 := by
      by_contra hn
      have h := quantitative_large_sum x y hx hy (by linarith)
      linarith
    have hbound := quantitative_small_sum x y hs
    have hpos : 0 < x + y + 2 := by linarith
    have hz : (x + y - 1) ^ 2 * (x + y + 2) = 0 := by
      have hnn : 0 ≤ (x + y - 1) ^ 2 * (x + y + 2) := by positivity
      linarith
    have hs0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt hpos))
    have hs1 : x + y = 1 := by linarith
    have hid := small_sum_identity x y
    rw [he, hs1] at hid
    have hd : (x - y) ^ 2 = 0 := by nlinarith [hid]
    have hxy := sq_eq_zero_iff.mp hd
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    unfold productGap
    ring

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (2 * x * y + x + y) * (x + y) + 1 - x * y ≥ 3 * (2 * x * y + x + y) / 2 := by
  have h := nonnegative_bound x y (le_of_lt hx) (le_of_lt hy)
  unfold productGap at h
  linarith
