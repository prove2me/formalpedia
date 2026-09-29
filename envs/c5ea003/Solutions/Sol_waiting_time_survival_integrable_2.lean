-- Prove2me | solution 2 for waiting_time_survival_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T22:08:38.355759+00:00
-- url     : https://prove2.me/submissions/0e52ec29-a804-4459-8dc6-b8bdaa564a50

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
open MeasureTheory Set Finset
open scoped BigOperators

theorem solution (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    MeasureTheory.IntegrableOn
      (fun t => ∑ k ∈ Finset.range (mp+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))
      (Set.Ioi (0:ℝ)) := by
  -- inline `term_integrable`: per-term integrability for k < N
  have hterm : ∀ k : ℕ, k < N →
      IntegrableOn (fun t : ℝ => (Nat.choose N k : ℝ)
        * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) (Ioi (0:ℝ)) := by
    intro k hk
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
  apply MeasureTheory.integrable_finset_sum (Finset.range (mp+1))
  intro k hk
  rw [Finset.mem_range] at hk
  exact hterm k (by omega)

#print axioms solution
