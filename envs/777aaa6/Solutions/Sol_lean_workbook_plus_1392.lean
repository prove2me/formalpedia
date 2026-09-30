-- Prove2me | solution 1 for lean_workbook_plus_1392
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:57:55.994183+00:00
-- url     : https://prove2.me/submissions/5487d783-b287-464e-8da7-67f1c011946a

import Mathlib

namespace FiveCycleLinearClassification

def System (y a b c d e : ℝ) : Prop :=
  e + b = y * a ∧ a + c = y * b ∧ b + d = y * c ∧ c + e = y * d ∧ d + a = y * e

def IsZero (a b c d e : ℝ) : Prop := a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0

def HasNonzeroSolution (y : ℝ) : Prop :=
  ∃ a b c d e : ℝ, System y a b c d e ∧ ¬ IsZero a b c d e

noncomputable def parameterVector (y : ℝ) (p : ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  (p.1, p.2, y * p.2 - p.1, -y * (p.1 + p.2), y * p.1 - p.2)

theorem zero_model (y : ℝ) : System y 0 0 0 0 0 := by
  unfold System
  simp

theorem constant_model (a : ℝ) : System 2 a a a a a := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem quadratic_model (y a b : ℝ) (hy : y ^ 2 + y - 1 = 0) :
    System y a b (y * b - a) (-y * (a + b)) (y * a - b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ring
  · ring
  · linear_combination -b * hy
  · linear_combination (a + b) * hy
  · linear_combination -a * hy

theorem sum_constraint (y a b c d e : ℝ) (h : System y a b c d e) :
    (y - 2) * (a + b + c + d + e) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  linear_combination -h1 - h2 - h3 - h4 - h5

theorem coordinate_annihilator (y a b c d e : ℝ) (h : System y a b c d e) :
    (y ^ 2 + y - 1) * a = a + b + c + d + e ∧
    (y ^ 2 + y - 1) * b = a + b + c + d + e ∧
    (y ^ 2 + y - 1) * c = a + b + c + d + e ∧
    (y ^ 2 + y - 1) * d = a + b + c + d + e ∧
    (y ^ 2 + y - 1) * e = a + b + c + d + e := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination -(y + 1) * h1 - h2 - h5
  · linear_combination -(y + 1) * h2 - h1 - h3
  · linear_combination -(y + 1) * h3 - h2 - h4
  · linear_combination -(y + 1) * h4 - h3 - h5
  · linear_combination -(y + 1) * h5 - h4 - h1

theorem at_two (a b c d e : ℝ) :
    System 2 a b c d e ↔ a = b ∧ b = c ∧ c = d ∧ d = e := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [h1, h2, h3, h4, h5]
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact constant_model _

theorem at_quadratic_root (y a b c d e : ℝ) (hy : y ^ 2 + y - 1 = 0) :
    System y a b c d e ↔ c = y * b - a ∧ d = -y * (a + b) ∧ e = y * a - b := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨?_, ?_, ?_⟩
    · linarith only [h2]
    · linear_combination h3 + y * h2 + b * hy
    · linarith only [h1]
  · rintro ⟨rfl, rfl, rfl⟩
    exact quadratic_model y a b hy

theorem off_spectrum (y a b c d e : ℝ) (hy2 : y ≠ 2) (hyq : y ^ 2 + y - 1 ≠ 0) :
    System y a b c d e ↔ IsZero a b c d e := by
  constructor
  · intro h
    have hs := (mul_eq_zero.mp (sum_constraint y a b c d e h)).resolve_left (sub_ne_zero.mpr hy2)
    have hc := coordinate_annihilator y a b c d e h
    rw [hs] at hc
    exact ⟨(mul_eq_zero.mp hc.1).resolve_left hyq,
      (mul_eq_zero.mp hc.2.1).resolve_left hyq,
      (mul_eq_zero.mp hc.2.2.1).resolve_left hyq,
      (mul_eq_zero.mp hc.2.2.2.1).resolve_left hyq,
      (mul_eq_zero.mp hc.2.2.2.2).resolve_left hyq⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact zero_model y

theorem classification (y a b c d e : ℝ) :
    System y a b c d e ↔
      (y = 2 ∧ a = b ∧ b = c ∧ c = d ∧ d = e) ∨
      (y ^ 2 + y - 1 = 0 ∧ c = y * b - a ∧ d = -y * (a + b) ∧ e = y * a - b) ∨
      IsZero a b c d e := by
  constructor
  · intro h
    by_cases hy2 : y = 2
    · subst y
      exact Or.inl ⟨rfl, (at_two a b c d e).mp h⟩
    · by_cases hyq : y ^ 2 + y - 1 = 0
      · exact Or.inr (Or.inl ⟨hyq, (at_quadratic_root y a b c d e hyq).mp h⟩)
      · exact Or.inr (Or.inr ((off_spectrum y a b c d e hy2 hyq).mp h))
  · rintro (⟨hy, h⟩ | ⟨hy, h⟩ | h)
    · subst y
      exact (at_two a b c d e).mpr h
    · exact (at_quadratic_root y a b c d e hy).mpr h
    · rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact zero_model y

theorem quadratic_roots (y : ℝ) :
    y ^ 2 + y - 1 = 0 ↔
      y = (-1 + Real.sqrt 5) / 2 ∨ y = (-1 - Real.sqrt 5) / 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  constructor
  · intro h
    have he : (2 * y + 1) ^ 2 = (Real.sqrt 5) ^ 2 := by nlinarith only [h, hs]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
    · exact Or.inl (by linarith only [h])
    · exact Or.inr (by linarith only [h])
  · rintro (rfl | rfl) <;> nlinarith only [hs]

theorem other_parameters (y a b c d e : ℝ) (hy2 : y ≠ 2)
    (hyp : y ≠ (-1 + Real.sqrt 5) / 2) (hym : y ≠ (-1 - Real.sqrt 5) / 2) :
    System y a b c d e ↔ IsZero a b c d e := by
  apply off_spectrum y a b c d e hy2
  intro h
  exact ((quadratic_roots y).mp h).elim hyp hym

theorem nonzero_iff (y : ℝ) : HasNonzeroSolution y ↔ y = 2 ∨ y ^ 2 + y - 1 = 0 := by
  constructor
  · rintro ⟨a, b, c, d, e, h, hn⟩
    rcases (classification y a b c d e).mp h with h | h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact False.elim (hn h)
  · rintro (rfl | hy)
    · refine ⟨1, 1, 1, 1, 1, constant_model 1, ?_⟩
      intro h
      have h1 := h.1
      norm_num at h1
    · refine ⟨1, 0, y * 0 - 1, -y * (1 + 0), y * 1 - 0, quadratic_model y 1 0 hy, ?_⟩
      intro h
      have h1 := h.1
      norm_num at h1

theorem explicit_nonzero_parameters (y : ℝ) : HasNonzeroSolution y ↔
    y = 2 ∨ y = (-1 + Real.sqrt 5) / 2 ∨ y = (-1 - Real.sqrt 5) / 2 := by
  rw [nonzero_iff, quadratic_roots]

theorem parameterVector_injective (y : ℝ) : Function.Injective (parameterVector y) := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun v : ℝ × ℝ × ℝ × ℝ × ℝ => v.1) h
  · exact congrArg (fun v : ℝ × ℝ × ℝ × ℝ × ℝ => v.2.1) h

end FiveCycleLinearClassification

theorem solution (y : ℝ) (x : ℕ → ℝ) :
    (∃ x₁ x₂ x₃ x₄ x₅ : ℝ,
      x₅ + x₂ = y * x₁ ∧ x₁ + x₃ = y * x₂ ∧ x₂ + x₄ = y * x₃ ∧
        x₃ + x₅ = y * x₄ ∧ x₄ + x₁ = y * x₅) ↔ (∃ x : ℝ, 2 * x = y) := by
  constructor
  · intro _
    exact ⟨y / 2, by ring⟩
  · intro _
    exact ⟨0, 0, 0, 0, 0, FiveCycleLinearClassification.zero_model y⟩

#print axioms FiveCycleLinearClassification.zero_model
#print axioms FiveCycleLinearClassification.constant_model
#print axioms FiveCycleLinearClassification.quadratic_model
#print axioms FiveCycleLinearClassification.sum_constraint
#print axioms FiveCycleLinearClassification.coordinate_annihilator
#print axioms FiveCycleLinearClassification.at_two
#print axioms FiveCycleLinearClassification.at_quadratic_root
#print axioms FiveCycleLinearClassification.off_spectrum
#print axioms FiveCycleLinearClassification.classification
#print axioms FiveCycleLinearClassification.quadratic_roots
#print axioms FiveCycleLinearClassification.other_parameters
#print axioms FiveCycleLinearClassification.nonzero_iff
#print axioms FiveCycleLinearClassification.explicit_nonzero_parameters
#print axioms FiveCycleLinearClassification.parameterVector_injective
#print axioms solution
