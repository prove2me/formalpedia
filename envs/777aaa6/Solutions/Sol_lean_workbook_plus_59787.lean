-- Prove2me | solution 1 for lean_workbook_plus_59787
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:27:37.145899+00:00
-- url     : https://prove2.me/submissions/cbc3752e-ae84-4fdf-9071-c3f5551db5ea

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem shifted_ratio_square_refinement (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    12 * (a ^ 2 + b ^ 2 + c ^ 2) ≤
      (8 * ((1 + a) * (1 + b) * (1 + c)) * (4 + a + b + c)) *
        (1 / 8 * (2 + a) * (2 + b) * (2 + c) / ((1 + a) * (1 + b) * (1 + c)) -
          (4 - a - b - c) / (4 + a + b + c)) := by
  have hda : 1 + a ≠ 0 := by positivity
  have hdb : 1 + b ≠ 0 := by positivity
  have hdc : 1 + c ≠ 0 := by positivity
  have hds : 4 + a + b + c ≠ 0 := by positivity
  have h : (8 * ((1 + a) * (1 + b) * (1 + c)) * (4 + a + b + c)) *
        (1 / 8 * (2 + a) * (2 + b) * (2 + c) / ((1 + a) * (1 + b) * (1 + c)) -
          (4 - a - b - c) / (4 + a + b + c)) =
      12 * (a ^ 2 + b ^ 2 + c ^ 2) +
      10 * (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b)) +
      2 * a * b * c + 9 * a * b * c * (a + b + c) := by
    field_simp [hda, hdb, hdc, hds]
    <;> ring
  have hp : 0 ≤ 10 * (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b)) +
      2 * a * b * c + 9 * a * b * c * (a + b + c) := by positivity
  linarith only [h, hp]

theorem shifted_ratio_equality_iff (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (1 / 8 * (2 + a) * (2 + b) * (2 + c) / ((1 + a) * (1 + b) * (1 + c)) =
      (4 - a - b - c) / (4 + a + b + c)) ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro he
    have h := shifted_ratio_square_refinement a b c ha hb hc
    rw [he, sub_self, mul_zero] at h
    exact ⟨by nlinarith [sq_nonneg b, sq_nonneg c],
      by nlinarith [sq_nonneg a, sq_nonneg c], by nlinarith [sq_nonneg a, sq_nonneg b]⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (1 / 8 * (2 + a) * (2 + b) * (2 + c) / ((1 + a) * (1 + b) * (1 + c))) ≥
      (4 - a - b - c) / (4 + a + b + c) := by
  have h := shifted_ratio_square_refinement a b c ha hb hc
  have hs : 0 ≤ 12 * (a ^ 2 + b ^ 2 + c ^ 2) := by positivity
  have hp : 0 < 8 * ((1 + a) * (1 + b) * (1 + c)) * (4 + a + b + c) := by positivity
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (le_trans hs h) hp)

#print axioms solution
#print axioms shifted_ratio_square_refinement
#print axioms shifted_ratio_equality_iff
