-- Prove2me | solution 1 for lean_workbook_plus_72962
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:03:36.324337+00:00
-- url     : https://prove2.me/submissions/a0f7a771-c896-4300-ac2d-c7712be22a16

import Mathlib

set_option autoImplicit false

namespace ParametricRationalQuadratic

noncomputable section

def discriminant (a : ℝ) : ℝ := a ^ 2 - 6 * a - 3

def lowerRoot (a : ℝ) : ℝ := (a - 1 - Real.sqrt (discriminant a)) / 2

def upperRoot (a : ℝ) : ℝ := (a - 1 + Real.sqrt (discriminant a)) / 2

theorem cleared_equation (a x : ℝ) (hx : x ≠ 0) :
    (x + a + 1) / x = a - x ↔ x ^ 2 - (a - 1) * x + a + 1 = 0 := by
  rw [div_eq_iff hx]
  constructor <;> intro h <;> nlinarith only [h]

theorem discriminant_of_root (a x : ℝ)
    (h : x ^ 2 - (a - 1) * x + a + 1 = 0) : 0 ≤ discriminant a := by
  dsimp [discriminant]
  nlinarith only [h, sq_nonneg (2 * x - a + 1)]

theorem quadratic_roots (a x : ℝ) (ha : 0 ≤ discriminant a) :
    x ^ 2 - (a - 1) * x + a + 1 = 0 ↔ x = lowerRoot a ∨ x = upperRoot a := by
  have hs := Real.sq_sqrt ha
  change Real.sqrt (discriminant a) ^ 2 = a ^ 2 - 6 * a - 3 at hs
  dsimp [lowerRoot, upperRoot]
  constructor
  · intro h
    have he : (2 * x - a + 1 + Real.sqrt (discriminant a)) *
        (2 * x - a + 1 - Real.sqrt (discriminant a)) = 0 := by
      nlinarith only [h, hs]
    rcases mul_eq_zero.mp he with he | he
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> nlinarith only [hs]

theorem root_sum_product (a : ℝ) (ha : 0 ≤ discriminant a) :
    lowerRoot a + upperRoot a = a - 1 ∧ lowerRoot a * upperRoot a = a + 1 := by
  have hs := Real.sq_sqrt ha
  change Real.sqrt (discriminant a) ^ 2 = a ^ 2 - 6 * a - 3 at hs
  dsimp [lowerRoot, upperRoot]
  constructor
  · ring
  · nlinarith only [hs]

theorem discriminant_region (a : ℝ) :
    0 ≤ discriminant a ↔ a ≤ 3 - Real.sqrt 12 ∨ 3 + Real.sqrt 12 ≤ a := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)
  have hp : 0 < Real.sqrt 12 := Real.sqrt_pos.mpr (by norm_num)
  dsimp [discriminant]
  constructor
  · intro h
    by_cases hl : a ≤ 3 - Real.sqrt 12
    · exact Or.inl hl
    · right
      by_contra hr
      have h1 : 0 < a - 3 + Real.sqrt 12 := by linarith
      have h2 : 0 < 3 + Real.sqrt 12 - a := by linarith
      nlinarith only [h, hs, mul_pos h1 h2]
  · rintro (h | h)
    · have h1 : 0 ≤ 3 - Real.sqrt 12 - a := by linarith
      have h2 : 0 ≤ 3 + Real.sqrt 12 - a := by linarith
      nlinarith only [hs, mul_nonneg h1 h2]
    · have h1 : 0 ≤ a - 3 - Real.sqrt 12 := by linarith
      have h2 : 0 ≤ a - 3 + Real.sqrt 12 := by linarith
      nlinarith only [hs, mul_nonneg h1 h2]

theorem complete_classification (a x : ℝ) :
    (x ≠ 0 ∧ (x + a + 1) / x = a - x) ↔
      0 ≤ discriminant a ∧ x ≠ 0 ∧ (x = lowerRoot a ∨ x = upperRoot a) := by
  constructor
  · rintro ⟨hx, h⟩
    have hq := (cleared_equation a x hx).mp h
    have ha := discriminant_of_root a x hq
    exact ⟨ha, hx, (quadratic_roots a x ha).mp hq⟩
  · rintro ⟨ha, hx, h⟩
    exact ⟨hx, (cleared_equation a x hx).mpr ((quadratic_roots a x ha).mpr h)⟩

theorem complete_solution_set (a : ℝ) (ha : 0 ≤ discriminant a) :
    {x : ℝ | x ≠ 0 ∧ (x + a + 1) / x = a - x} =
      ({lowerRoot a, upperRoot a} : Set ℝ) \ {0} := by
  ext x
  simp only [Set.mem_setOf_eq, complete_classification, ha, true_and,
    Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem solvable_iff (a : ℝ) :
    (∃ x : ℝ, x ≠ 0 ∧ (x + a + 1) / x = a - x) ↔
      a ≤ 3 - Real.sqrt 12 ∨ 3 + Real.sqrt 12 ≤ a := by
  rw [← discriminant_region]
  constructor
  · rintro ⟨x, hx, h⟩
    exact (complete_classification a x).mp ⟨hx, h⟩ |>.1
  · intro ha
    by_cases hl : lowerRoot a = 0
    · have hu : upperRoot a ≠ 0 := by
        intro hu
        obtain ⟨hs, hp⟩ := root_sum_product a ha
        rw [hl, hu] at hs hp
        linarith
      exact ⟨upperRoot a, (complete_classification a _).mpr
        ⟨ha, hu, Or.inr rfl⟩⟩
    · exact ⟨lowerRoot a, (complete_classification a _).mpr
        ⟨ha, hl, Or.inl rfl⟩⟩

theorem zero_is_quadratic_root_iff (a : ℝ) :
    (0 : ℝ) ^ 2 - (a - 1) * 0 + a + 1 = 0 ↔ a = -1 := by
  constructor <;> intro h <;> linarith

theorem negative_one_classification (x : ℝ) :
    (x ≠ 0 ∧ (x + (-1) + 1) / x = -1 - x) ↔ x = -2 := by
  constructor
  · rintro ⟨hx, h⟩
    have hq := (cleared_equation (-1) x hx).mp h
    have he : x * (x + 2) = 0 := by nlinarith only [hq]
    have hh := (mul_eq_zero.mp he).resolve_left hx
    linarith
  · rintro rfl
    norm_num

theorem seven_classification (x : ℝ) :
    (x ≠ 0 ∧ (x + 7 + 1) / x = 7 - x) ↔ x = 2 ∨ x = 4 := by
  constructor
  · rintro ⟨hx, h⟩
    have hq := (cleared_equation 7 x hx).mp h
    have he : (x - 2) * (x - 4) = 0 := by nlinarith only [hq]
    rcases mul_eq_zero.mp he with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

theorem totalized_division_classification (a x : ℝ) :
    (x + a + 1) / x = a - x ↔
      (x = 0 ∧ a = 0) ∨
      (0 ≤ discriminant a ∧ x ≠ 0 ∧ (x = lowerRoot a ∨ x = upperRoot a)) := by
  by_cases hx : x = 0
  · subst x
    simp [eq_comm]
  · have h := complete_classification a x
    simpa [hx] using h

end

end ParametricRationalQuadratic

theorem solution {x a : ℝ} (h₁ : x ≠ 0) (h₂ : a = 7) :
    (x + a + 1) / x = a - x ↔ x ^ 2 - (a - 1) * x + a + 1 = 0 := by
  exact ParametricRationalQuadratic.cleared_equation a x h₁

#print axioms ParametricRationalQuadratic.discriminant
#print axioms ParametricRationalQuadratic.lowerRoot
#print axioms ParametricRationalQuadratic.upperRoot
#print axioms ParametricRationalQuadratic.cleared_equation
#print axioms ParametricRationalQuadratic.discriminant_of_root
#print axioms ParametricRationalQuadratic.quadratic_roots
#print axioms ParametricRationalQuadratic.root_sum_product
#print axioms ParametricRationalQuadratic.discriminant_region
#print axioms ParametricRationalQuadratic.complete_classification
#print axioms ParametricRationalQuadratic.complete_solution_set
#print axioms ParametricRationalQuadratic.solvable_iff
#print axioms ParametricRationalQuadratic.zero_is_quadratic_root_iff
#print axioms ParametricRationalQuadratic.negative_one_classification
#print axioms ParametricRationalQuadratic.seven_classification
#print axioms ParametricRationalQuadratic.totalized_division_classification
#print axioms solution
