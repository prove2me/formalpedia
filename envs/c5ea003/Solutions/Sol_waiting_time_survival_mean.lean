-- Prove2me | solution 1 for waiting_time_survival_mean
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T19:40:17.176962+00:00
-- url     : https://prove2.me/submissions/b225fb72-3ce3-4c2c-82fa-4b240746f26a

import Theorems.Thm_waiting_survival_per_term_integral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
open MeasureTheory Set Finset
open scoped BigOperators

namespace SurvivalMean

-- per-term integrability (k < N so N-k ≥ 1)
theorem term_integrable (N k : ℕ) (lam : ℝ) (hlam : 0 < lam) (hk : k < N) :
    IntegrableOn (fun t : ℝ => (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) (Ioi (0:ℝ)) := by
  set C : ℝ := |(Nat.choose N k : ℝ)| with hC
  have hgint : IntegrableOn (fun t : ℝ => C * Real.exp (-lam * t)) (Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -lam) (c := (0:ℝ)) (by linarith)
    exact this.const_mul C
  have hcont : Continuous (fun t : ℝ => (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) := by fun_prop
  refine Integrable.mono' hgint hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Set.mem_Ioi] at ht
  have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
  have he1 : Real.exp (-(lam * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [ht, hlam]
  have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * t)) := by linarith
  have hq1 : 1 - Real.exp (-(lam * t)) ≤ 1 := by linarith [he.le]
  have hpm : (1 - Real.exp (-(lam * t))) ^ k ≤ 1 := pow_le_one₀ hq0 hq1
  have hNk : 1 ≤ N - k := by omega
  have hpe : (Real.exp (-(lam * t))) ^ (N - k) ≤ Real.exp (-(lam * t)) := by
    calc (Real.exp (-(lam * t))) ^ (N - k)
        ≤ (Real.exp (-(lam * t))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNk
      _ = Real.exp (-(lam * t)) := by rw [pow_one]
  have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * t))) ^ (N - k) := pow_nonneg he.le _
  rw [Real.norm_eq_abs]
  have hrw : |(Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k
      * (Real.exp (-(lam * t))) ^ (N - k)|
      = C * ((1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) := by
    rw [hC]
    rw [show (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (Nat.choose N k : ℝ) * ((1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) by ring]
    rw [abs_mul, abs_of_nonneg (a := (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) (by positivity)]
  rw [hrw, show C * Real.exp (-lam * t) = C * Real.exp (-(lam * t)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by rw [hC]; exact abs_nonneg _)
  calc (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      ≤ 1 * Real.exp (-(lam * t)) := mul_le_mul hpm hpe hpe0 (by norm_num)
    _ = Real.exp (-(lam * t)) := by ring

-- per-term value WITH the binomial coefficient:  ∫ C(N,k)(1-e)^k e^{N-k} = (1/λ)/(N-k)
theorem per_term_coef (N k : ℕ) (lam : ℝ) (hlam : 0 < lam) (hk : k < N) :
    ∫ t in Ioi (0:ℝ), (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (1 / lam) * (1 / ((N - k : ℕ) : ℝ)) := by
  have hfac : (∫ t in Ioi (0:ℝ), (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))
      = (Nat.choose N k : ℝ) * ∫ t in Ioi (0:ℝ),
          (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _; ring
  rw [hfac, waiting_survival_per_term_integral N k lam hlam hk]
  -- C(N,k) * (1/λ) * (k!(N-k-1)!/N!) = (1/λ)/(N-k)
  -- use C(N,k) = N!/(k!(N-k)!), and (N-k)! = (N-k)*(N-k-1)!
  have hchoose : (Nat.choose N k : ℝ) = (Nat.factorial N : ℝ)
      / ((Nat.factorial k : ℝ) * (Nat.factorial (N - k) : ℝ)) := by
    have hk' : k ≤ N := le_of_lt hk
    have := Nat.choose_mul_factorial_mul_factorial hk'
    have hcast := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at hcast
    have hkf : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hnkf : (Nat.factorial (N-k) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
    linarith [hcast]
  rw [hchoose]
  have hNk : N - k = (N - k - 1) + 1 := by omega
  have hfsucc : Nat.factorial (N - k) = (N - k) * Nat.factorial (N - k - 1) := by
    conv_lhs => rw [hNk]
    rw [Nat.factorial_succ]
    congr 1; omega
  rw [hfsucc]
  have hkf : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hnk1f : (Nat.factorial (N-k-1) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hNf : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hNkpos : ((N - k : ℕ) : ℝ) ≠ 0 := by
    have h0 : 0 < N - k := by omega
    exact_mod_cast h0.ne'
  push_cast
  field_simp

/-- **Survival-function integral = harmonic-tail / λ.** The integral over (0,∞) of the
binomial survival function (lower partial sum, $k=0..m$) of the waiting-time model equals
$(1/λ)·∑_{k=0}^{m} 1/(N-k)$. For a nonnegative random variable this is $E[T]$ (mean of the
waiting time), the genuine harmonic mean identity. -/
theorem survival_mean (N m : ℕ) (lam : ℝ) (hlam : 0 < lam) (hm : m < N) :
    ∫ t in Ioi (0:ℝ), ∑ k ∈ Finset.range (m+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (1 / lam) * ∑ k ∈ Finset.range (m+1), (1 / ((N - k : ℕ) : ℝ)) := by
  have hint : ∀ k ∈ Finset.range (m+1), IntegrableOn (fun t : ℝ => (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) (Ioi (0:ℝ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact term_integrable N k lam hlam (by omega)
  rw [MeasureTheory.integral_finset_sum (Finset.range (m+1)) hint]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact per_term_coef N k lam hlam (by omega)

end SurvivalMean

theorem solution (N m : ℕ) (lam : ℝ) (hlam : 0 < lam) (hm : m < N) :
    ∫ t in Set.Ioi (0:ℝ), ∑ k ∈ Finset.range (m+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (1 / lam) * ∑ k ∈ Finset.range (m+1), (1 / ((N - k : ℕ) : ℝ)) :=
  SurvivalMean.survival_mean N m lam hlam hm
