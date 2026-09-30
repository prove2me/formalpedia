-- Prove2me | solution 1 for lean_workbook_plus_58230
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:25:28.519331+00:00
-- url     : https://prove2.me/submissions/dfaa725b-10fc-46e0-b020-05654f5ef4f2

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace EllipseQuadraticRange

theorem necessary (a b t : ℝ) (h₁ : a ^ 2 + a * b + b ^ 2 = 1)
    (h₂ : t = a * b - a ^ 2 - b ^ 2) : -3 ≤ t ∧ t ≤ -1 / 3 := by
  constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]

theorem range_iff (t : ℝ) :
    (∃ a b : ℝ, a ^ 2 + a * b + b ^ 2 = 1 ∧ t = a * b - a ^ 2 - b ^ 2) ↔
      -3 ≤ t ∧ t ≤ -1 / 3 := by
  constructor
  · rintro ⟨a, b, h₁, h₂⟩
    exact necessary a b t h₁ h₂
  · rintro ⟨hl, hu⟩
    have hp : 0 ≤ (t + 3) / 2 := by linarith
    have hq : 0 ≤ (-3 * t - 1) / 2 := by linarith
    have hs := Real.sq_sqrt hp
    have hr := Real.sq_sqrt hq
    refine ⟨(Real.sqrt ((t + 3) / 2) + Real.sqrt ((-3 * t - 1) / 2)) / 2,
      (Real.sqrt ((t + 3) / 2) - Real.sqrt ((-3 * t - 1) / 2)) / 2, ?_, ?_⟩
    · nlinarith
    · nlinarith

theorem endpoint_characterization (a b t : ℝ)
    (h₁ : a ^ 2 + a * b + b ^ 2 = 1) (h₂ : t = a * b - a ^ 2 - b ^ 2) :
    (t = -3 ↔ a + b = 0) ∧ (t = -1 / 3 ↔ a = b) := by
  constructor
  · constructor
    · intro ht
      have hs : (a + b) ^ 2 = 0 := by nlinarith
      exact eq_zero_of_pow_eq_zero hs
    · intro hab
      nlinarith
  · constructor
    · intro ht
      have hs : (a - b) ^ 2 = 0 := by nlinarith
      exact eq_of_sub_eq_zero (eq_zero_of_pow_eq_zero hs)
    · intro hab
      rw [hab] at h₁ h₂
      nlinarith

end EllipseQuadraticRange

theorem solution (a b t : ℝ) (h₁ : a ^ 2 + a * b + b ^ 2 = 1)
    (h₂ : t = a * b - a ^ 2 - b ^ 2) :
    ∃ a b, a ^ 2 + a * b + b ^ 2 = 1 ∧ t = a * b - a ^ 2 - b ^ 2 :=
  (EllipseQuadraticRange.range_iff t).mpr (EllipseQuadraticRange.necessary a b t h₁ h₂)
