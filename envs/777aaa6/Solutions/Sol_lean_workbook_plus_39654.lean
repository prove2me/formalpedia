-- Prove2me | solution 1 for lean_workbook_plus_39654
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:25:33.553137+00:00
-- url     : https://prove2.me/submissions/22cb0cf0-fe60-4ce1-a3fc-97494f98c6d6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution    (a b c : ℝ)
    (h₁ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₂ : c < a + b)
    (h₃ : b < a + c)
    (h₄ : a < b + c) :
    0 ≤ a^2 * (b / c - 1) + b^2 * (c / a - 1) + c^2 * (a / b - 1)   := by
  rcases h₁ with ⟨ha, hb, hc⟩
  let x := a + c - b
  let y := a + b - c
  let z := b + c - a
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  let N := a^3*b^2+b^3*c^2+c^3*a^2-a*b*c*(a^2+b^2+c^2)
  have hid : 32 * N = x*(x^2-y^2)^2+y*(y^2-z^2)^2+z*(z^2-x^2)^2 := by
    dsimp [N, x, y, z]
    ring
  have hN : 0 ≤ N := by
    nlinarith only [hid, mul_nonneg hx (sq_nonneg (x^2-y^2)), mul_nonneg hy (sq_nonneg (y^2-z^2)), mul_nonneg hz (sq_nonneg (z^2-x^2))]
  have hr : a^2*(b/c-1)+b^2*(c/a-1)+c^2*(a/b-1) = N/(a*b*c) := by
    dsimp [N]
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
    ring
  rw [hr]
  exact div_nonneg hN (by positivity)
