-- Prove2me | solution 1 for lean_workbook_plus_6948
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:46:09.377939+00:00
-- url     : https://prove2.me/submissions/a20ca495-d197-4fc5-ba8e-6944549c54e5

import Mathlib

namespace QuarticFiveNodeInterpolation

def samples (a b c d e : ℝ) : Prop :=
  a * 2 ^ 4 + b * 2 ^ 3 + c * 2 ^ 2 + d * 2 + e = -2 ∧
  a + b + c + d + e = -2 ∧
  a * (-1) ^ 4 + b * (-1) ^ 3 + c * (-1) ^ 2 + d * (-1) + e = -2 ∧
  a * (-2) ^ 4 + b * (-2) ^ 3 + c * (-2) ^ 2 + d * (-2) + e = 14 ∧
  a * 3 ^ 4 + b * 3 ^ 3 + c * 3 ^ 2 + d * 3 + e = 14

theorem coefficients_iff (a b c d e : ℝ) :
    samples a b c d e ↔
      a = 2 / 3 ∧ b = -4 / 3 ∧ c = -2 / 3 ∧ d = 4 / 3 ∧ e = -2 := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    ring_nf at h1 h2 h3 h4 h5
    change a * 16 + b * 8 + c * 4 + d * 2 + e = -2 at h1
    change a - b + (c - d) + e = -2 at h3
    change a * 16 - b * 8 + (c * 4 - d * 2) + e = 14 at h4
    change a * 81 + b * 27 + c * 9 + d * 3 + e = 14 at h5
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem factorization (a b c d e : ℝ) (h : samples a b c d e) (x : ℝ) :
    a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e + 2 =
      (2 / 3 : ℝ) * x * (x - 2) * (x - 1) * (x + 1) := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := (coefficients_iff a b c d e).mp h
  ring

theorem level_set (a b c d e : ℝ) (h : samples a b c d e) (x : ℝ) :
    a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e = -2 ↔
      x = 0 ∨ x = 2 ∨ x = 1 ∨ x = -1 := by
  have hf := factorization a b c d e h x
  constructor
  · intro hx
    have hz : (2 / 3 : ℝ) * x * (x - 2) * (x - 1) * (x + 1) = 0 := by
      linarith
    simpa [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg, or_assoc] using hz
  · intro hx
    have hz : (2 / 3 : ℝ) * x * (x - 2) * (x - 1) * (x + 1) = 0 := by
      rcases hx with rfl | rfl | rfl | rfl <;> ring
    linarith

theorem unique_existence : ∃! v : ℝ × ℝ × ℝ × ℝ × ℝ,
    samples v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 := by
  refine ⟨(2 / 3, -4 / 3, -2 / 3, 4 / 3, -2), ?_, ?_⟩
  · exact (coefficients_iff _ _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨a, b, c, d, e⟩ h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := (coefficients_iff a b c d e).mp h
    rfl

end QuarticFiveNodeInterpolation

theorem solution (a b c d e f : ℝ)
    (h₁ : a * 2 ^ 4 + b * 2 ^ 3 + c * 2 ^ 2 + d * 2 + e = -2)
    (h₂ : a + b + c + d + e = -2)
    (h₃ : a * (-1) ^ 4 + b * (-1) ^ 3 + c * (-1) ^ 2 + d * (-1) + e = -2)
    (h₄ : a * (-2) ^ 4 + b * (-2) ^ 3 + c * (-2) ^ 2 + d * (-2) + e = 14)
    (h₅ : a * 3 ^ 4 + b * 3 ^ 3 + c * 3 ^ 2 + d * 3 + e = 14) :
    a * 0 ^ 4 + b * 0 ^ 3 + c * 0 ^ 2 + d * 0 + e = -2 := by
  have h := (QuarticFiveNodeInterpolation.coefficients_iff a b c d e).mp
    ⟨h₁, h₂, h₃, h₄, h₅⟩
  simpa using h.2.2.2.2

#print axioms QuarticFiveNodeInterpolation.coefficients_iff
#print axioms QuarticFiveNodeInterpolation.factorization
#print axioms QuarticFiveNodeInterpolation.level_set
#print axioms QuarticFiveNodeInterpolation.unique_existence
#print axioms solution
