-- Prove2me | solution 1 for lean_workbook_plus_59543
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:04:28.118093+00:00
-- url     : https://prove2.me/submissions/e55900bb-0e2a-4251-b0cc-ede8c75dadc0

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace WeightedReciprocalConstraint

theorem cleared_constraint (a b : ℝ) (ha : -1 < a) (hb : -1 < b)
    (h : 2 / (1 + a) + 5 / (1 + b) ≤ 1) :
    2 * (1 + b) + 5 * (1 + a) ≤ (1 + a) * (1 + b) := by
  have hu : 0 < 1 + a := by linarith
  have hv : 0 < 1 + b := by linarith
  have hm := mul_le_mul_of_nonneg_right h (le_of_lt (mul_pos hu hv))
  have hid : (2 / (1 + a) + 5 / (1 + b)) * ((1 + a) * (1 + b)) =
      2 * (1 + b) + 5 * (1 + a) := by
    field_simp [ne_of_gt hu, ne_of_gt hv]
    <;> ring
  rw [hid, one_mul] at hm
  exact hm

theorem bound (a b : ℝ) (ha : -1 < a) (hb : -1 < b)
    (h : 2 / (1 + a) + 5 / (1 + b) ≤ 1) : 33 ≤ 5 * a + 2 * b := by
  have hc := cleared_constraint a b ha hb h
  have ht : 0 < 5 * (1 + a) + 2 * (1 + b) := by linarith
  have hs := sq_nonneg (5 * (1 + a) - 2 * (1 + b))
  nlinarith

theorem equality_iff (a b : ℝ) (ha : -1 < a) (hb : -1 < b)
    (h : 2 / (1 + a) + 5 / (1 + b) ≤ 1) :
    5 * a + 2 * b = 33 ↔ a = 3 ∧ b = 9 := by
  constructor
  · intro he
    have hc := cleared_constraint a b ha hb h
    have ht : 5 * (1 + a) + 2 * (1 + b) = 40 := by linarith
    have hs : 5 * (1 + a) = 2 * (1 + b) := by
      nlinarith [sq_nonneg (5 * (1 + a) - 2 * (1 + b))]
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem attained : 2 / (1 + (3 : ℝ)) + 5 / (1 + (9 : ℝ)) ≤ 1 ∧
    5 * (3 : ℝ) + 2 * 9 = 33 := by norm_num

end WeightedReciprocalConstraint

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 / (1 + a) + 5 / (1 + b) ≤ 1 → 5 * a + 2 * b ≥ 33 := by
  exact WeightedReciprocalConstraint.bound a b (by linarith) (by linarith)
