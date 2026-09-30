-- Prove2me | solution 1 for lean_workbook_plus_61046
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:28:23.171066+00:00
-- url     : https://prove2.me/submissions/b8951aad-b1eb-4202-a9c7-aea179b766de

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

theorem rational_two_variable_gap (x y : ℝ) :
    2 * ((1 + x ^ 2) * (1 + y ^ 2) - (x - y) * (1 - x * y)) =
      (x - y - (1 - x * y)) ^ 2 + (1 + x * y) ^ 2 + (x + y) ^ 2 := by ring

theorem solution (x y : ℝ) :
    (x - y) * (1 - x * y) / ((1 + x ^ 2) * (1 + y ^ 2)) ≤ 1 := by
  apply (div_le_one (by positivity : 0 < (1 + x ^ 2) * (1 + y ^ 2))).2
  nlinarith [rational_two_variable_gap x y, sq_nonneg (x - y - (1 - x * y)),
    sq_nonneg (1 + x * y), sq_nonneg (x + y)]

theorem rational_two_variable_lower (x y : ℝ) :
    -1 ≤ (x - y) * (1 - x * y) / ((1 + x ^ 2) * (1 + y ^ 2)) := by
  have h := solution y x
  have hn : (y - x) * (1 - y * x) / ((1 + y ^ 2) * (1 + x ^ 2)) =
      -((x - y) * (1 - x * y) / ((1 + x ^ 2) * (1 + y ^ 2))) := by ring
  rw [hn] at h
  linarith

theorem rational_two_variable_max_equality (x y : ℝ) :
    (x - y) * (1 - x * y) / ((1 + x ^ 2) * (1 + y ^ 2)) = 1 ↔
      x = 1 ∧ y = -1 := by
  constructor
  · intro h
    have hd : (1 + x ^ 2) * (1 + y ^ 2) ≠ 0 := by positivity
    have he := (div_eq_one_iff_eq hd).mp h
    have hi := rational_two_variable_gap x y
    have hsq1 := sq_nonneg (x - y - (1 - x * y))
    have hsq2 := sq_nonneg (1 + x * y)
    have hsq3 := sq_nonneg (x + y)
    have h1 : (x - y - (1 - x * y)) ^ 2 = 0 := by nlinarith
    have h2 : (1 + x * y) ^ 2 = 0 := by nlinarith
    have h3 : (x + y) ^ 2 = 0 := by nlinarith
    have he1 := sq_eq_zero_iff.mp h1
    have he2 := sq_eq_zero_iff.mp h2
    have he3 := sq_eq_zero_iff.mp h3
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    ring

theorem rational_two_variable_min_equality (x y : ℝ) :
    (x - y) * (1 - x * y) / ((1 + x ^ 2) * (1 + y ^ 2)) = -1 ↔
      x = -1 ∧ y = 1 := by
  have hn : (y - x) * (1 - y * x) / ((1 + y ^ 2) * (1 + x ^ 2)) =
      -((x - y) * (1 - x * y) / ((1 + x ^ 2) * (1 + y ^ 2))) := by ring
  have he := rational_two_variable_max_equality y x
  rw [hn] at he
  constructor
  · intro h
    have hp := he.mp (by linarith)
    exact ⟨hp.2, hp.1⟩
  · rintro ⟨rfl, rfl⟩
    ring

theorem rational_two_variable_attainment :
    (1 - (-1 : ℝ)) * (1 - 1 * (-1 : ℝ)) / ((1 + (1 : ℝ) ^ 2) * (1 + (-1 : ℝ) ^ 2)) = 1 ∧
      ((-1 : ℝ) - 1) * (1 - (-1 : ℝ) * 1) / ((1 + (-1 : ℝ) ^ 2) * (1 + (1 : ℝ) ^ 2)) = -1 := by
  constructor <;> ring

#print axioms solution
#print axioms rational_two_variable_gap
#print axioms rational_two_variable_lower
#print axioms rational_two_variable_max_equality
#print axioms rational_two_variable_min_equality
#print axioms rational_two_variable_attainment
