-- Prove2me | solution 1 for beta_nat_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T19:28:06.898223+00:00
-- url     : https://prove2.me/submissions/65e55ad0-a498-468a-a8ff-67df65178dc6

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
open scoped BigOperators
open intervalIntegral MeasureTheory

namespace BetaNat

-- base case: ∫₀¹ (1-u)^j = 1/(j+1)
theorem beta_base (j : ℕ) :
    ∫ u in (0:ℝ)..1, (1 - u) ^ j = 1 / (j + 1) := by
  have hjne : ((j:ℝ)+1) ≠ 0 := by positivity
  have hd : ∀ u ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => (-(1 / ((j:ℝ)+1))) * (1 - u) ^ (j+1)) ((1 - u) ^ j) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => (1 - u) ^ (j+1))
        (-(((j+1 : ℕ) : ℝ) * (1 - u) ^ j)) u := by
      have hb : HasDerivAt (fun u : ℝ => (1 - u)) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub 1
      have := (hasDerivAt_pow (j+1) (1 - u)).comp u hb
      simp only [Nat.add_sub_cancel] at this
      convert this using 1
      push_cast; ring
    have h2 := h1.const_mul (-(1 / ((j:ℝ)+1)))
    convert h2 using 1
    push_cast
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [sub_self]
  rw [zero_pow (by omega : j+1 ≠ 0)]
  simp only [sub_zero, one_pow, mul_one, mul_zero]
  field_simp
  ring

-- recurrence: ∫₀¹ u^{k+1}(1-u)^j = ((k+1)/(j+1)) ∫₀¹ u^k (1-u)^{j+1}
theorem beta_rec (k j : ℕ) :
    ∫ u in (0:ℝ)..1, u ^ (k+1) * (1 - u) ^ j
      = ((k+1 : ℝ) / (j+1)) * ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ (j+1) := by
  have hjne : ((j:ℝ)+1) ≠ 0 := by positivity
  -- U = u^{k+1}, U' = (k+1) u^k ;  V = -(1-u)^{j+1}/(j+1), V' = (1-u)^j
  set U : ℝ → ℝ := fun u => u ^ (k+1) with hU
  set U' : ℝ → ℝ := fun u => ((k+1 : ℕ) : ℝ) * u ^ k with hU'
  set V : ℝ → ℝ := fun u => (-(1 / ((j:ℝ)+1))) * (1 - u) ^ (j+1) with hV
  set V' : ℝ → ℝ := fun u => (1 - u) ^ j with hV'
  have hUd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt U (U' x) x := by
    intro x _; simpa [hU, hU'] using hasDerivAt_pow (k+1) x
  have hVd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt V (V' x) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => (1 - u) ^ (j+1))
        (-(((j+1 : ℕ) : ℝ) * (1 - x) ^ j)) x := by
      have hb : HasDerivAt (fun u : ℝ => (1 - u)) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      have := (hasDerivAt_pow (j+1) (1 - x)).comp x hb
      simp only [Nat.add_sub_cancel] at this
      convert this using 1; push_cast; ring
    have h2 := h1.const_mul (-(1 / ((j:ℝ)+1)))
    simp only [hV, hV']
    convert h2 using 1
    push_cast; field_simp
  have hU'int : IntervalIntegrable U' MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable; rw [hU']; fun_prop
  have hV'int : IntervalIntegrable V' MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable; rw [hV']; fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hUd hVd hU'int hV'int
  -- hibp : ∫ U x * V' x = U 1 * V 1 - U 0 * V 0 - ∫ U' x * V x
  -- boundary = 0
  have hb1 : U 1 * V 1 = 0 := by simp [hU, hV]
  have hb0 : U 0 * V 0 = 0 := by simp [hU]
  rw [hb1, hb0] at hibp
  simp only [sub_zero, zero_sub] at hibp
  -- LHS of hibp = ∫ u^{k+1}(1-u)^j
  have hlhs : (∫ x in (0:ℝ)..1, U x * V' x) = ∫ u in (0:ℝ)..1, u ^ (k+1) * (1 - u) ^ j := by
    apply intervalIntegral.integral_congr; intro x _; simp [hU, hV']
  -- RHS integrand: U' x * V x = (k+1) u^k * (-(1/(j+1)))(1-u)^{j+1}
  have hrhs : (∫ x in (0:ℝ)..1, U' x * V x)
      = (-(((k+1:ℕ):ℝ)/((j:ℝ)+1))) * ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ (j+1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro x _
    simp only [hU', hV]; push_cast; ring
  rw [hlhs, hrhs] at hibp
  rw [hibp]
  push_cast; ring

-- full Beta-at-naturals:  ∫₀¹ u^k(1-u)^j = k! j! / (k+j+1)!
theorem beta_nat (k j : ℕ) :
    ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ j
      = (Nat.factorial k * Nat.factorial j : ℝ) / Nat.factorial (k + j + 1) := by
  induction k generalizing j with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.zero_add]
    rw [beta_base j]
    rw [Nat.factorial_succ j]
    have hj1 : ((j:ℝ)+1) ≠ 0 := by positivity
    have hfac : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp
  | succ k ih =>
    rw [beta_rec k j, ih (j+1)]
    rw [Nat.factorial_succ (k), Nat.factorial_succ (j)]
    have he : (k+1) + j + 1 = k + (j+1) + 1 := by omega
    rw [he]
    have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
    have hj1 : ((j:ℝ)+1) ≠ 0 := by positivity
    have hfac : (Nat.factorial (k + (j+1) + 1) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp

end BetaNat

theorem solution (k j : ℕ) :
    ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ j
      = (Nat.factorial k * Nat.factorial j : ℝ) / Nat.factorial (k + j + 1) :=
  BetaNat.beta_nat k j
