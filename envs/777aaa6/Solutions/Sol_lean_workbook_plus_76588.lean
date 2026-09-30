-- Prove2me | solution 1 for lean_workbook_plus_76588
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:28:47.287964+00:00
-- url     : https://prove2.me/submissions/af723fa8-415e-406a-896f-b4af7d01001b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a ≥ b ∧ b ≥ c) :
    a * b / (a + b) + b * c / (b + c) + c * a / (c + a) ≤
      (3 * (a * b + b * c + c * a)) / (2 * (a + b + c)) := by
  obtain ⟨ha, hb, hc⟩ := h₀
  have hs : 0 < a + b + c := by positivity
  have hab : 0 < a + b := by positivity
  have hbc : 0 < b + c := by positivity
  have hca : 0 < c + a := by positivity
  have hpoly : 0 ≤ (a + b + c) * (a * b + b * c + c * a) ^ 2 -
      3 * (a * b + b * c + c * a) * (a * b * c) -
      2 * (a + b + c) ^ 2 * (a * b * c) := by
    let x := a - b
    let y := b - c
    have hx : 0 ≤ x := sub_nonneg.mpr h₁.1
    have hy : 0 ≤ y := sub_nonneg.mpr h₁.2
    have ha' : a = x + y + c := by dsimp [x, y]; ring
    have hb' : b = y + c := by dsimp [y]; ring
    rw [ha', hb']
    clear_value x y
    convert (show (0 : ℝ) ≤
      x ^ 3 * (y ^ 2 + 2 * y * c + 2 * c ^ 2) +
      x ^ 2 * (4 * y ^ 3 + 10 * y ^ 2 * c + 9 * y * c ^ 2 + 4 * c ^ 3) +
      x * y * (5 * y ^ 3 + 16 * y ^ 2 * c + 15 * y * c ^ 2 + 4 * c ^ 3) +
      2 * y ^ 2 * (y + c) ^ 2 * (y + 2 * c) by positivity) using 1 <;> ring
  have identity :
      ((3 * (a * b + b * c + c * a)) / (2 * (a + b + c)) -
        (a * b / (a + b) + b * c / (b + c) + c * a / (c + a))) *
        (2 * (a + b + c) * ((a + b) * (b + c) * (c + a))) =
      (a + b + c) * (a * b + b * c + c * a) ^ 2 -
        3 * (a * b + b * c + c * a) * (a * b * c) -
        2 * (a + b + c) ^ 2 * (a * b * c) := by
    field_simp [ne_of_gt hs, ne_of_gt hab, ne_of_gt hbc, ne_of_gt hca]
    <;> ring
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left
    (b := 2 * (a + b + c) * ((a + b) * (b + c) * (c + a)))
    (by rw [identity]; exact hpoly) (by positivity)

#print axioms solution
