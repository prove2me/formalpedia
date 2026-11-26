-- Prove2me | solution 1 for ReweightedNPMLE.gamma_lower_tail_exact
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:10:59.825266+00:00
-- url     : https://prove2.me/submissions/ef001b28-5119-4fe9-98bc-24f4297c698d

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_centered_gamma_mgf
import Theorems.Thm_ReweightedNPMLE_exponential_markov_lower
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
/-- Optimized lower Chernoff bound for a shape--rate `Gamma(a,a)` law. -/
theorem solution {a t : ℝ} (ha : 0 < a) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    (gammaMeasure a a).real {x | x ≤ 1 - t} ≤
      Real.exp (-a * (-t - Real.log (1 - t))) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  rcases ht₀.eq_or_lt with rfl | htpos
  · simpa using (measureReal_le_one : (gammaMeasure a a).real {x | x ≤ 1} ≤ 1)
  · let s : ℝ := a * t / (1 - t)
    have hden : 0 < 1 - t := sub_pos.mpr ht₁
    have hs : 0 < s := by dsimp [s]; positivity
    have hneglt : -s < a := by linarith
    have hint := integrable_centered_gamma_exp ha hneglt
    have hmark := exponential_markov_lower (gammaMeasure a a)
      (fun x ↦ x - 1) hs hint (c := t)
    have hset : {x : ℝ | x - 1 ≤ -t} = {x : ℝ | x ≤ 1 - t} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hx <;> linarith
    rw [hset] at hmark
    have hmgf := centered_gamma_mgf ha hneglt
    have hfun : (fun x : ℝ ↦ Real.exp (-s * (x - 1))) =
        (fun x ↦ Real.exp ((-s) * (x - 1))) := by
      funext x
      congr 1
    rw [hfun, hmgf] at hmark
    calc
      (gammaMeasure a a).real {x | x ≤ 1 - t} ≤
          Real.exp (-s * t) * (Real.exp (-(-s)) * (1 - (-s) / a) ^ (-a)) := hmark
      _ = Real.exp (-a * (-t - Real.log (1 - t))) := by
        have ha0 : a ≠ 0 := ha.ne'
        have hbase : 1 - (-s) / a = (1 - t)⁻¹ := by
          dsimp [s]
          field_simp
          ring
        rw [hbase, Real.rpow_def_of_pos (inv_pos.mpr hden), Real.log_inv]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [s]
        field_simp
        ring
