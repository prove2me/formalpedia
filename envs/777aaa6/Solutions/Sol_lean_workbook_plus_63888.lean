-- Prove2me | solution 1 for lean_workbook_plus_63888
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:02:36.994825+00:00
-- url     : https://prove2.me/submissions/eaa0e520-682c-4982-8cb8-8c661023f560

import Mathlib

namespace QuadraticEqualValueReflection

def quadratic {R : Type*} [CommRing R] (a b c x : R) : R := a * x ^ 2 + b * x + c

theorem coefficient_iff {R : Type*} [CommRing R] [NoZeroDivisors R]
    (a b c u v : R) (hne : u ≠ v) :
    quadratic a b c u = quadratic a b c v ↔ b = -a * (u + v) := by
  constructor
  · intro h
    have hz : (u - v) * (a * (u + v) + b) = 0 := by
      unfold quadratic at h
      linear_combination h
    have he := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
    linear_combination he
  · intro h
    subst b
    unfold quadratic
    ring

theorem reflection {R : Type*} [CommRing R] [NoZeroDivisors R]
    (a b c u v : R) (hne : u ≠ v)
    (h : quadratic a b c u = quadratic a b c v) (x : R) :
    quadratic a b c (u + v - x) = quadratic a b c x := by
  have hb := (coefficient_iff a b c u v hne).mp h
  subst b
  unfold quadratic
  ring

theorem difference_factorization {R : Type*} [CommRing R] [NoZeroDivisors R]
    (a b c u v : R) (hne : u ≠ v)
    (h : quadratic a b c u = quadratic a b c v) (x : R) :
    quadratic a b c x - quadratic a b c u = a * (x - u) * (x - v) := by
  have hb := (coefficient_iff a b c u v hne).mp h
  subst b
  unfold quadratic
  ring

theorem level_set {R : Type*} [CommRing R] [NoZeroDivisors R]
    (a b c u v : R) (hne : u ≠ v) (ha : a ≠ 0)
    (h : quadratic a b c u = quadratic a b c v) (x : R) :
    quadratic a b c x = quadratic a b c u ↔ x = u ∨ x = v := by
  rw [← sub_eq_zero, difference_factorization a b c u v hne h x]
  simp only [mul_eq_zero, ha, false_or, sub_eq_zero]

theorem source_coefficient (k : ℝ) :
    3 * 1 ^ 2 + k * 1 + 117 = 3 * 10 ^ 2 + k * 10 + 117 ↔ k = -33 := by
  change quadratic (3 : ℝ) k 117 1 = quadratic 3 k 117 10 ↔ k = -33
  rw [coefficient_iff 3 k 117 1 10 (by norm_num)]
  norm_num

theorem source_factorization (k : ℝ) (hk : k = -33) (x : ℝ) :
    3 * x ^ 2 + k * x + 117 = 3 * (x - 1) * (x - 10) + 87 := by
  subst k
  ring

theorem source_minimum (x : ℝ) :
    105 / 4 ≤ 3 * x ^ 2 - 33 * x + 117 ∧
      (3 * x ^ 2 - 33 * x + 117 = 105 / 4 ↔ x = 11 / 2) := by
  have hs := sq_nonneg (x - 11 / 2)
  refine ⟨by nlinarith, ?_⟩
  constructor
  · intro h
    nlinarith
  · rintro rfl
    ring

end QuadraticEqualValueReflection

theorem solution (p : ℝ → ℝ) (k : ℝ)
    (h₁ : p = fun x : ℝ => 3 * x ^ 2 + k * x + 117) (h₂ : p 1 = p 10) :
    p 20 = 657 := by
  subst p
  have hk := (QuadraticEqualValueReflection.source_coefficient k).mp h₂
  subst k
  ring

#print axioms QuadraticEqualValueReflection.coefficient_iff
#print axioms QuadraticEqualValueReflection.reflection
#print axioms QuadraticEqualValueReflection.difference_factorization
#print axioms QuadraticEqualValueReflection.level_set
#print axioms QuadraticEqualValueReflection.source_coefficient
#print axioms QuadraticEqualValueReflection.source_factorization
#print axioms QuadraticEqualValueReflection.source_minimum
#print axioms solution
