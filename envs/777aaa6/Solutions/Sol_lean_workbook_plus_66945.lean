-- Prove2me | solution 1 for lean_workbook_plus_66945
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:55.320646+00:00
-- url     : https://prove2.me/submissions/8ec82f85-1137-4414-8dd5-41c33007243a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem weighted_tangent_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 5 + b ^ 3 ≤ a ^ 2 + b ^ 2) : 3 * a + b ≤ 4 := by
  have h₁ := mul_nonneg (sq_nonneg (a - 1))
    (show 0 ≤ a ^ 3 + 2 * a ^ 2 + 3 * a + 3 by positivity)
  have h₂ := mul_nonneg (sq_nonneg (b - 1)) (show 0 ≤ b + 1 by linarith)
  nlinarith

theorem nonnegative_constrained_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 5 + b ^ 3 ≤ a ^ 2 + b ^ 2) : a * (a + b) ≤ 2 := by
  have hw := weighted_tangent_bound a b ha hb hab
  have hp := mul_nonneg ha (show 0 ≤ 4 - 3 * a - b by linarith)
  nlinarith [sq_nonneg (a - 1)]

theorem constrained_equality (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 5 + b ^ 3 ≤ a ^ 2 + b ^ 2) :
    a * (a + b) = 2 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    have hw := weighted_tangent_bound a b ha hb hab
    have hp := mul_nonneg ha (show 0 ≤ 4 - 3 * a - b by linarith)
    have he : a = 1 := by nlinarith [sq_nonneg (a - 1)]
    exact ⟨he, by rw [he] at h; linarith⟩
  · rintro ⟨rfl, rfl⟩
    ring

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ^ 5 + b ^ 3 ≤ a ^ 2 + b ^ 2) : a * (a + b) ≤ 2 :=
  nonnegative_constrained_bound a b ha.le hb.le hab
