-- Prove2me | solution 1 for lean_workbook_plus_31005
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:59:48.603345+00:00
-- url     : https://prove2.me/submissions/86396f7c-fc40-44fe-946a-87002efd3a85

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b + b * c + c * a + 2 * a * b * c = 1) :
  a * b * c ≤ 1 / 8   := by
  obtain ⟨ha, hb, hc⟩ := h₀
  have amgm : ∀ u v w : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → 27 * u * v * w ≤ (u + v + w) ^ 3 := by
    intro u v w hu hv hw
    have hA := mul_nonneg (sq_nonneg (u + v - 2 * w)) (show 0 ≤ u + v + w / 4 by positivity)
    have hB := mul_nonneg hw (sq_nonneg (u - v))
    nlinarith
  let r : ℝ := a * b * c
  have hr : 0 < r := by dsimp [r]; positivity
  have hq : a * b + b * c + c * a = 1 - 2 * r := by dsimp [r]; linarith
  have hcube : 27 * r ^ 2 ≤ (1 - 2 * r) ^ 3 := by
    calc
      27 * r ^ 2 = 27 * (a * b) * (b * c) * (c * a) := by dsimp [r]; ring
      _ ≤ (a * b + b * c + c * a) ^ 3 := amgm (a * b) (b * c) (c * a) (by positivity) (by positivity) (by positivity)
      _ = (1 - 2 * r) ^ 3 := by rw [hq]
  change r ≤ 1 / 8
  by_contra hn
  have hpos : 0 < (8 * r - 1) * (1 + r) ^ 2 := by
    apply mul_pos
    · linarith
    · positivity
  nlinarith
