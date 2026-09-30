-- Prove2me | solution 1 for lean_workbook_plus_7234
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:53:55.113294+00:00
-- url     : https://prove2.me/submissions/465d8da1-6b2a-47cd-b03a-6b13fb2a60f7

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Polynomial

theorem parameter_classification (a b : ℝ)
    (h : ∀ x : ℝ, (a*x^3-7*x^2-10*x+24)*(2*x^5+2*x^4+b*x^3+5*x^2) =
      2*a*x^8-2*b*x^7-24*x^6+(b-a)*x^5-37*x^4+7*a*b*x^3+12*a*b*x^2) :
    a = 2 ∧ b = 5 := by
  let P : ℝ[X] :=
    (C a*X^3-C 7*X^2-C 10*X+C 24)*(C 2*X^5+C 2*X^4+C b*X^3+C 5*X^2)
  let Q : ℝ[X] :=
    C (2*a)*X^8-C (2*b)*X^7-C 24*X^6+C (b-a)*X^5-C 37*X^4+
      C (7*a*b)*X^3+C (12*a*b)*X^2
  have he : P = Q := by
    apply Polynomial.funext
    intro x
    simpa only [P, Q, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C] using h x
  have h7 := congrArg (fun p : ℝ[X] => p.coeff 7) he
  have h5 := congrArg (fun p : ℝ[X] => p.coeff 5) he
  simp only [Q, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul_X_pow] at h7 h5
  dsimp [P] at h7 h5
  rw [Polynomial.coeff_mul] at h7 h5
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at h7 h5
  norm_num at h7 h5
  change (-14:ℝ)+a*2 = -(2*b) at h7
  change (28:ℝ)+-(7*b)+a*5 = (0:ℝ)+(b-a) at h5
  constructor <;> linarith only [h7, h5]

theorem parameters_satisfy : ∀ x : ℝ,
    (2*x^3-7*x^2-10*x+24)*(2*x^5+2*x^4+5*x^3+5*x^2) =
      2*2*x^8-2*5*x^7-24*x^6+(5-2)*x^5-37*x^4+7*2*5*x^3+12*2*5*x^2 := by
  intro x
  ring

theorem solution (a b : ℝ)
    (h : ∀ x : ℝ, (a*x^3-7*x^2-10*x+24)*(2*x^5+2*x^4+b*x^3+5*x^2) =
      2*a*x^8-2*b*x^7-24*x^6+(b-a)*x^5-37*x^4+7*a*b*x^3+12*a*b*x^2) :
    a+b = 7 := by
  obtain ⟨rfl, rfl⟩ := parameter_classification a b h
  norm_num
