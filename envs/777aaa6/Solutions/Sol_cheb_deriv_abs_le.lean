-- Prove2me | solution 1 for cheb_deriv_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T11:37:18.415096+00:00
-- url     : https://prove2.me/submissions/996fb265-b60c-49cc-b7a6-c74a89b04a73

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Group.Abs

open Polynomial Polynomial.Chebyshev

namespace ChebDeriv

/-- `|T_n(c)| ≤ 1` for `c ∈ [-1,1]`. -/
lemma T_abs_le_one (n : ℤ) (c : ℝ) (hc1 : -1 ≤ c) (hc2 : c ≤ 1) :
    |(T ℝ n).eval c| ≤ 1 := by
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos hc1 hc2
  have := T_real_cos (Real.arccos c) n
  rw [hcos] at this
  rw [this]
  exact Real.abs_cos_le_one _

/-- `|U_n(c)| ≤ n + 1` for `c ∈ [-1,1]`, `n : ℕ`. -/
lemma U_abs_le (n : ℕ) (c : ℝ) (hc1 : -1 ≤ c) (hc2 : c ≤ 1) :
    |(U ℝ (n : ℤ)).eval c| ≤ (n : ℝ) + 1 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, Int.cast_zero, U_zero, Polynomial.eval_one, abs_one, zero_add, le_refl]
  | succ m ih =>
    -- U_eq_X_mul_U_add_T R m : U R (m+1) = X * U R m + T R (m+1)
    have hrec := U_eq_X_mul_U_add_T ℝ (m : ℤ)
    have hcabs : |c| ≤ 1 := abs_le.mpr ⟨hc1, hc2⟩
    have hcastm1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    rw [hcastm1]
    calc |(U ℝ ((m : ℤ) + 1)).eval c|
        = |c * (U ℝ (m : ℤ)).eval c + (T ℝ ((m : ℤ) + 1)).eval c| := by
          rw [hrec]; simp [Polynomial.eval_add, Polynomial.eval_mul]
      _ ≤ |c * (U ℝ (m : ℤ)).eval c| + |(T ℝ ((m : ℤ) + 1)).eval c| := abs_add_le _ _
      _ = |c| * |(U ℝ (m : ℤ)).eval c| + |(T ℝ ((m : ℤ) + 1)).eval c| := by rw [abs_mul]
      _ ≤ 1 * ((m : ℝ) + 1) + 1 := by
          apply add_le_add
          · apply mul_le_mul hcabs ih (abs_nonneg _) (by norm_num)
          · exact T_abs_le_one _ c hc1 hc2
      _ = (m : ℝ) + 1 + 1 := by ring
      _ = ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

end ChebDeriv

open ChebDeriv

theorem solution : cheb_deriv_abs_le := by
  intro d c hc1 hc2
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: T_0 = 1, derivative = 0.
    subst hd0
    simp only [Nat.cast_zero, Int.cast_zero, T_zero, Polynomial.derivative_one,
      Polynomial.eval_zero, abs_zero]
    norm_num
  · -- d ≥ 1: T'_d = d * U_{d-1}, |U_{d-1}| ≤ d.
    have hderiv := T_derivative_eq_U (R := ℝ) (d : ℤ)
    have hd1 : (d : ℤ) - 1 = ((d - 1 : ℕ) : ℤ) := by omega
    rw [hd1] at hderiv
    have hUbd := U_abs_le (d - 1) c hc1 hc2
    have hd1r : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
      have : (1 : ℕ) ≤ d := hdpos
      push_cast [Nat.cast_sub this]
      ring
    rw [hd1r] at hUbd
    calc |(derivative (T ℝ (d : ℤ))).eval c|
        = |(d : ℝ) * (U ℝ ((d - 1 : ℕ) : ℤ)).eval c| := by
          rw [hderiv]
          simp [Polynomial.eval_mul]
      _ = (d : ℝ) * |(U ℝ ((d - 1 : ℕ) : ℤ)).eval c| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (d:ℝ))]
      _ ≤ (d : ℝ) * (d : ℝ) := by
          apply mul_le_mul_of_nonneg_left hUbd (by positivity)
      _ = (d : ℝ)^2 := by ring
