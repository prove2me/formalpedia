-- Prove2me | solution 1 for lean_workbook_plus_59436
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:18:40.473466+00:00
-- url     : https://prove2.me/submissions/665ce42e-0402-4c87-91f4-be4b556913cd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem triangle_quadratic_gap_identity (a b c : ℝ) :
    4 * (a ^ 2 + (b - a) * (c - a)) - 3 * a ^ 2 =
      (a + b - c) * (a + c - b) + (b + c - 2 * a) ^ 2 := by
  ring

theorem triangle_quadratic_strict_bound (a b c : ℝ)
    (hab : c < a + b) (hac : b < a + c) :
    3 / 4 * a ^ 2 < a ^ 2 + (b - a) * (c - a) := by
  have hid := triangle_quadratic_gap_identity a b c
  have hp := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hac)
  nlinarith [sq_nonneg (b + c - 2 * a)]

theorem triangle_quadratic_degenerate_bound (a b c : ℝ)
    (hab : c ≤ a + b) (hac : b ≤ a + c) :
    3 / 4 * a ^ 2 ≤ a ^ 2 + (b - a) * (c - a) ∧
    (a ^ 2 + (b - a) * (c - a) = 3 / 4 * a ^ 2 ↔
      (b = a / 2 ∧ c = 3 * a / 2) ∨ (b = 3 * a / 2 ∧ c = a / 2)) := by
  have hid := triangle_quadratic_gap_identity a b c
  have hp := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hac)
  have hs := sq_nonneg (b + c - 2 * a)
  constructor
  · nlinarith
  · constructor
    · intro he
      have hs0 : b + c - 2 * a = 0 := sq_eq_zero_iff.mp (by nlinarith)
      have hp0 : (a + b - c) * (a + c - b) = 0 := by nlinarith
      rcases mul_eq_zero.mp hp0 with hbc | hcb
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring

theorem triangle_quadratic_coefficient_optimal (k : ℝ) (hk : 3 / 4 < k) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c < a + b ∧ b < a + c ∧
      a < b + c ∧ a ^ 2 + (b - a) * (c - a) < k * a ^ 2 := by
  let t := min (1 / 2) (k - 3 / 4)
  have ht : 0 < t := lt_min (by norm_num) (sub_pos.mpr hk)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htk : t ≤ k - 3 / 4 := min_le_right _ _
  refine ⟨2, 1 + t, 3 - t, by norm_num, by linarith, by linarith,
    by linarith, by linarith, by linarith, ?_⟩
  nlinarith [sq_nonneg t]

theorem solution : ∀ a b c : ℝ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a →
      a ^ 2 + (b - a) * (c - a) > 0 := by
  intro a b c h
  have hb := triangle_quadratic_strict_bound a b c h.2.2.2.1 h.2.2.2.2.1
  nlinarith [sq_nonneg a]

#print axioms solution
#print axioms triangle_quadratic_gap_identity
#print axioms triangle_quadratic_strict_bound
#print axioms triangle_quadratic_degenerate_bound
#print axioms triangle_quadratic_coefficient_optimal
