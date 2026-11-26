-- Prove2me | solution 1 for ReweightedNPMLE.real_exp_taylor_remainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:52:37.8949+00:00
-- url     : https://prove2.me/submissions/680194c5-01eb-4d77-b99b-7756642ab51a

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic

-- Inline helpers preserved from ReweightedNPMLE.Taylor.
section
/-!
# Quantitative exponential approximation

Exact Taylor and factorial bounds used in Proposition 4.1 and Lemma 8.1 of the manuscript.
-/

namespace ReweightedNPMLE

open Finset Set

private lemma taylorWithinEval_exp_zero (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    taylorWithinEval Real.exp m (uIcc 0 t) 0 t =
      ∑ ell ∈ range (m + 1), t ^ ell / ell.factorial := by
  rw [taylor_within_apply]
  apply sum_congr rfl
  intro ell _
  have hu : UniqueDiffOn ℝ (uIcc 0 t) := uniqueDiffOn_Icc (by grind)
  rw [iteratedDerivWithin_eq_iteratedDeriv hu Real.contDiff_exp.contDiffAt left_mem_uIcc]
  have hderiv : iteratedDeriv ell Real.exp 0 = 1 := by
    have h := congrFun (iteratedDeriv_exp_const_mul ell 1) 0
    simpa using h
  rw [hderiv]
  simp only [sub_zero, smul_eq_mul, mul_one, div_eq_mul_inv]
  ring





end ReweightedNPMLE
end

/-!
# Quantitative exponential approximation

Exact Taylor and factorial bounds used in Proposition 4.1 and Lemma 8.1 of the manuscript.
-/

open ReweightedNPMLE

open Finset Set
open ReweightedNPMLE in
/-- Uniform Lagrange remainder bound for the exponential series on `[-T,T]`. -/
theorem solution (m : ℕ) {t T : ℝ}
    (hT : 0 ≤ T) (ht : |t| ≤ T) :
    |Real.exp t - ∑ ell ∈ range (m + 1), t ^ ell / ell.factorial| ≤
      Real.exp T * T ^ (m + 1) / (m + 1).factorial := by
  by_cases ht0 : t = 0
  · subst t
    simp [sum_range_succ']
    positivity
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (x := t) (x₀ := 0) (Ne.symm ht0)
      (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ (m + 1) Real.exp (uIcc 0 t))
  rw [taylorWithinEval_exp_zero m ht0] at hrem
  have hderiv : iteratedDeriv (m + 1) Real.exp ξ = Real.exp ξ := by
    have h := congrFun (iteratedDeriv_exp_const_mul (m + 1) 1) ξ
    simpa using h
  rw [hrem, hderiv]
  have hξ_abs : |ξ| ≤ |t| := by
    simpa using abs_sub_left_of_mem_uIcc ⟨hξ.1.le, hξ.2.le⟩
  have hξT : ξ ≤ T := le_trans (le_abs_self ξ) (hξ_abs.trans ht)
  simp only [sub_zero, abs_div, abs_mul, abs_pow, Real.abs_exp, Nat.abs_cast]
  gcongr
