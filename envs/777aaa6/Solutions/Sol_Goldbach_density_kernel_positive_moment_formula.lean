-- Prove2me | solution 1 for Goldbach.density_kernel_positive_moment_formula
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:21:30.754871+00:00
-- url     : https://prove2.me/submissions/59ece5c6-9d42-4f13-b8b8-e6be20165a2a

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory
set_option autoImplicit false

private lemma expanded_moment (n : ℕ) :
    (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*u^n) =
    (16/15:ℝ)*2^(n+1)/(n+1) - (4/3:ℝ)*2^(n+3)/(n+3) +
    (2/3:ℝ)*2^(n+4)/(n+4) - (1/30:ℝ)*2^(n+6)/(n+6) := by
  have hp (k : ℕ) : IntervalIntegrable (fun u : ℝ => u^k) volume 0 2 :=
    (continuous_id.pow k).intervalIntegrable 0 2
  have he : (fun u : ℝ => ((2-u)^3*(4+6*u+u^2)/30)*u^n) =
      (fun u : ℝ => (16/15)*u^n-(4/3)*u^(n+2)+(2/3)*u^(n+3)-(1/30)*u^(n+5)) := by
    funext u
    simp only [pow_add]
    ring
  rw [he]
  have h1 := (hp n).const_mul (16/15:ℝ)
  have h2 := (hp (n+2)).const_mul (4/3:ℝ)
  have h3 := (hp (n+3)).const_mul (2/3:ℝ)
  have h4 := (hp (n+5)).const_mul (1/30:ℝ)
  rw [intervalIntegral.integral_sub ((h1.sub h2).add h3) h4,
    intervalIntegral.integral_add (h1.sub h2) h3,
    intervalIntegral.integral_sub h1 h2]
  simp only [intervalIntegral.integral_const_mul,integral_pow,
    zero_pow (Nat.add_pos_right _ (by omega))]
  push_cast
  ring

theorem solution (n : ℕ) :
    (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*u^n) =
      4*(2:ℝ)^(n+4)/(5*((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)*((n:ℝ)+4)) +
      6*(2:ℝ)^(n+5)/(5*((n:ℝ)+2)*((n:ℝ)+3)*((n:ℝ)+4)*((n:ℝ)+5)) +
      (2:ℝ)^(n+6)/(5*((n:ℝ)+3)*((n:ℝ)+4)*((n:ℝ)+5)*((n:ℝ)+6)) := by
  rw [expanded_moment]
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  have h3 : (n:ℝ)+3 ≠ 0 := by positivity
  have h4 : (n:ℝ)+4 ≠ 0 := by positivity
  have h5 : (n:ℝ)+5 ≠ 0 := by positivity
  have h6 : (n:ℝ)+6 ≠ 0 := by positivity
  simp only [pow_add]
  norm_num
  field_simp
  ring

#print axioms solution
