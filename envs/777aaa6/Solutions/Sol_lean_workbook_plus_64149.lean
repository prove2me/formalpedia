-- Prove2me | solution 1 for lean_workbook_plus_64149
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:24:07.554419+00:00
-- url     : https://prove2.me/submissions/c2e94097-4483-4395-8872-1dc0384beb97

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

def triangleCubicGap (a b c : ℝ) : ℝ :=
  a ^ 3 + b ^ 3 + 2 * (a + b) * c ^ 2 -
    (c ^ 3 + 2 * (a ^ 2 + b ^ 2) * c + a * b * c)

theorem triangle_cubic_gap_identity (a b c : ℝ) :
    2 * triangleCubicGap a b c =
      (a + b - c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) := by
  unfold triangleCubicGap
  ring

theorem triangle_cubic_gap_nonnegative (a b c : ℝ) (hc : c ≤ a + b) :
    0 ≤ triangleCubicGap a b c := by
  have hs : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 :=
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hp := mul_nonneg (sub_nonneg.mpr hc) hs
  linarith [triangle_cubic_gap_identity a b c]

theorem triangle_cubic_gap_zero_iff (a b c : ℝ) :
    triangleCubicGap a b c = 0 ↔ a + b = c ∨ (a = b ∧ b = c) := by
  have hi := triangle_cubic_gap_identity a b c
  constructor
  · intro h
    have hp : (a + b - c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) = 0 := by
      linarith
    rcases mul_eq_zero.mp hp with hz | hz
    · exact Or.inl (by linarith)
    · right
      constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  · rintro (h | ⟨h, h'⟩)
    · have hz : a + b - c = 0 := by linarith
      rw [hz, zero_mul] at hi
      linarith
    · rw [h, h']
      unfold triangleCubicGap
      ring

theorem solution (a b c : ℝ) (hx : a > 0 ∧ b > 0 ∧ c > 0)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    a ^ 3 + b ^ 3 + 2 * (a + b) * c ^ 2 ≥
      c ^ 3 + 2 * (a ^ 2 + b ^ 2) * c + a * b * c := by
  have h := triangle_cubic_gap_nonnegative a b c hab.le
  unfold triangleCubicGap at h
  linarith

#print axioms solution
#print axioms triangle_cubic_gap_nonnegative
#print axioms triangle_cubic_gap_zero_iff
