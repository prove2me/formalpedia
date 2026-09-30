-- Prove2me | solution 1 for lean_workbook_plus_75396
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:51:56.035288+00:00
-- url     : https://prove2.me/submissions/e574b40d-ef30-4b76-88b4-3aab78bd3224

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

theorem nonsquare_quadratic_coordinates {K : Type*} [Field K]
    (d : K) (hd : ¬ IsSquare d) (u v : K) (h : u ^ 2 = d * v ^ 2) :
    u = 0 ∧ v = 0 := by
  have hv : v = 0 := by
    by_contra hv
    have hq : (u / v) ^ 2 = d := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hv)]
      exact h
    exact hd ⟨u / v, by simpa only [pow_two] using hq.symm⟩
  have hu : u ^ 2 = 0 := by simpa [hv] using h
  exact ⟨by simpa using hu, hv⟩

theorem two_matrix_quadratic_determinant {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (d : K) :
    Matrix.det (A ^ 2 - d • (1 : Matrix (Fin 2) (Fin 2) K)) =
      (Matrix.det A + d) ^ 2 - d * (A 0 0 + A 1 1) ^ 2 := by
  simp [Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, pow_two, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

theorem two_matrix_nonsquare_quadratic {K : Type*} [Field K]
    (d : K) (hd : ¬ IsSquare d) (A : Matrix (Fin 2) (Fin 2) K)
    (h : Matrix.det (A ^ 2 - d • (1 : Matrix (Fin 2) (Fin 2) K)) = 0) :
    A ^ 2 = d • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hi := two_matrix_quadratic_determinant A d
  rw [h] at hi
  have hq : (Matrix.det A + d) ^ 2 = d * (A 0 0 + A 1 1) ^ 2 :=
    sub_eq_zero.mp hi.symm
  obtain ⟨hdet, htrace⟩ :=
    nonsquare_quadratic_coordinates d hd (Matrix.det A + d) (A 0 0 + A 1 1) hq
  simp only [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
  · linear_combination A 0 0 * htrace - hdet
  · linear_combination A 0 1 * htrace
  · linear_combination A 1 0 * htrace
  · linear_combination A 1 1 * htrace - hdet

theorem rational_matrix_full_source (A : Matrix (Fin 2) (Fin 2) ℚ)
    (h : Matrix.det (A ^ 2 - (2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) = 0) :
    A ^ 2 = (2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  have h2 : ¬ IsSquare (2 : ℚ) := by
    intro hs
    exact Nat.prime_two.not_isSquare (Rat.isSquare_natCast_iff.mp hs)
  exact two_matrix_nonsquare_quadratic 2 h2 A h

theorem solution {A : Matrix (Fin 2) (Fin 2) ℚ}
    (hA : A ^ 2 - 2 • (1 : Matrix (Fin 2) (Fin 2) ℚ) = 0) :
    A ^ 2 = 2 • (1 : Matrix (Fin 2) (Fin 2) ℚ) :=
  sub_eq_zero.mp hA

#print axioms solution
#print axioms two_matrix_nonsquare_quadratic
#print axioms rational_matrix_full_source
