-- Prove2me | solution 1 for lean_workbook_plus_69315
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:48:05.935544+00:00
-- url     : https://prove2.me/submissions/fe34e374-a235-45dc-a81d-1cc6ab867a99

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

theorem corrected_quartic_factorization (z : ℂ) :
    z ^ 4 - 4 * z ^ 2 - z + 2 = (z - 2) * (z + 1) * (z ^ 2 + z - 1) := by
  ring

theorem golden_quadratic_factorization (z : ℂ) :
    z ^ 2 + z - 1 =
      (z - (-1 + (Real.sqrt 5 : ℂ)) / 2) * (z - (-1 - (Real.sqrt 5 : ℂ)) / 2) := by
  have hs : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  linear_combination hs / 4

theorem corrected_quartic_roots (z : ℂ) :
    z ^ 4 - 4 * z ^ 2 - z + 2 = 0 ↔
      z = 2 ∨ z = -1 ∨ z = (-1 + (Real.sqrt 5 : ℂ)) / 2 ∨
        z = (-1 - (Real.sqrt 5 : ℂ)) / 2 := by
  rw [corrected_quartic_factorization, golden_quadratic_factorization]
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]

theorem corrected_quartic_roots_real (z : ℂ)
    (hz : z ^ 4 - 4 * z ^ 2 - z + 2 = 0) : z.im = 0 := by
  rcases (corrected_quartic_roots z).mp hz with rfl | rfl | rfl | rfl <;> simp

theorem golden_quadratic_no_rational_root (q : ℚ) : q ^ 2 + q - 1 ≠ 0 := by
  intro hq
  have hr : (q : ℝ) ^ 2 + q - 1 = 0 := by exact_mod_cast hq
  have he : (2 * (q : ℝ) + 1) ^ 2 = 5 := by nlinarith
  have ha : |2 * (q : ℝ) + 1| = Real.sqrt 5 := by
    rw [← Real.sqrt_sq_eq_abs, he]
  have hi : Irrational (Real.sqrt 5) :=
    (show Nat.Prime 5 by norm_num).irrational_sqrt
  apply hi
  refine ⟨|2 * q + 1|, ?_⟩
  simpa only [Rat.cast_abs, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] using ha

theorem golden_quadratic_irreducible :
    Irreducible (Polynomial.X ^ 2 + Polynomial.X - 1 : Polynomial ℚ) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (Polynomial.X ^ 2 + Polynomial.X - 1 : Polynomial ℚ).natDegree = 2 := by
      compute_degree!
    simp [hd]
  · intro q hq
    apply golden_quadratic_no_rational_root q
    simpa [Polynomial.IsRoot] using hq

theorem solution : ¬ (∀ x : ℂ,
    x ^ 4 - 4 * x ^ 2 - x + 2 = (x - 2) * (x + 1) * (x ^ 2 + x + 1)) := by
  intro h
  have h0 := h 0
  have hc : (4 : ℂ) = 0 := by linear_combination h0
  norm_num at hc

#print axioms corrected_quartic_factorization
#print axioms corrected_quartic_roots
#print axioms corrected_quartic_roots_real
#print axioms golden_quadratic_no_rational_root
#print axioms golden_quadratic_irreducible
#print axioms solution
