-- Prove2me | solution 1 for ReweightedNPMLE.gamma_upper_tail_exact
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:11:14.688172+00:00
-- url     : https://prove2.me/submissions/94f8415b-7b1f-41ac-a198-abb430cab7b1

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_centered_gamma_mgf
import Theorems.Thm_ReweightedNPMLE_exponential_markov_upper
import Theorems.Thm_ReweightedNPMLE_integrable_exp_mul_gammaMeasure

-- Inline helpers preserved from ReweightedNPMLE.GammaDistribution.
section
/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

namespace ReweightedNPMLE























/-- Integrability companion to `centered_gamma_mgf`. -/
theorem integrable_centered_gamma_exp {a t : ℝ} (ha : 0 < a) (ht : t < a) :
    Integrable (fun x ↦ Real.exp (t * (x - 1))) (gammaMeasure a a) := by
  have h := (integrable_exp_mul_gammaMeasure ha ha ht).const_mul (Real.exp (-t))
  apply h.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change Real.exp (-t) * Real.exp (t * x) = Real.exp (t * (x - 1))
    rw [← Real.exp_add]
    congr 1
    ring





















end ReweightedNPMLE
end

/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Optimized upper Chernoff bound for a shape--rate `Gamma(a,a)` law. -/
theorem solution {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (gammaMeasure a a).real {x | 1 + t ≤ x} ≤
      Real.exp (-a * (t - Real.log (1 + t))) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  rcases ht.eq_or_lt with rfl | htpos
  · simpa using (measureReal_le_one : (gammaMeasure a a).real {x | 1 ≤ x} ≤ 1)
  · let s : ℝ := a * t / (1 + t)
    have hden : 0 < 1 + t := by linarith
    have hs : 0 < s := by dsimp [s]; positivity
    have hslt : s < a := by
      dsimp [s]
      rw [div_lt_iff₀ hden]
      nlinarith
    have hint := integrable_centered_gamma_exp ha hslt
    have hmark := exponential_markov_upper (gammaMeasure a a)
      (fun x ↦ x - 1) hs hint (c := t)
    have hset : {x : ℝ | t ≤ x - 1} = {x : ℝ | 1 + t ≤ x} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hx <;> linarith
    rw [hset, centered_gamma_mgf ha hslt] at hmark
    calc
      (gammaMeasure a a).real {x | 1 + t ≤ x} ≤
          Real.exp (-s * t) * (Real.exp (-s) * (1 - s / a) ^ (-a)) := hmark
      _ = Real.exp (-a * (t - Real.log (1 + t))) := by
        have ha0 : a ≠ 0 := ha.ne'
        have hbase : 1 - s / a = (1 + t)⁻¹ := by
          dsimp [s]
          field_simp
          ring
        rw [hbase, Real.rpow_def_of_pos (inv_pos.mpr hden), Real.log_inv]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [s]
        field_simp
        ring
