-- Prove2me | solution 1 for ReweightedNPMLE.gaussianLocationMixtureSample_max_radius_tail
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:10:19.740583+00:00
-- url     : https://prove2.me/submissions/799776cf-5044-4604-9a91-963e90b24a76

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Theorems.Thm_ReweightedNPMLE_gaussianLocationMixtureLaw_radius_tail

/-!
# Gaussian radius bounds

Chernoff and finite-union estimates for the radius event in the likelihood-net
argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Radius union bound for `n` independent draws from any compactly bounded
Gaussian location mixture. -/
theorem solution
    {d n : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    {S t : ℝ} (hϑS : ∀ a, ‖ϑ a‖ ≤ S) (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n ↦ gaussianLocationMixtureLaw μ ϑ)).real
        {x : Fin n → Point d |
          ∃ k, ‖x k‖ > S + Real.sqrt d * t} ≤
      2 * n * d * Real.exp (-t ^ 2 / 2) := by
  let ν := gaussianLocationMixtureLaw μ ϑ
  letI : IsProbabilityMeasure ν :=
    gaussianLocationMixtureLaw_isProbability μ ϑ hϑmeas
  let νn : Measure (Fin n → Point d) := Measure.pi (fun _ : Fin n ↦ ν)
  have hcoord (k : Fin n) :
      νn.real {x : Fin n → Point d |
          ‖x k‖ > S + Real.sqrt d * t} ≤
        2 * d * Real.exp (-t ^ 2 / 2) := by
    have hmeas : MeasurableSet
        {x : Point d | ‖x‖ > S + Real.sqrt d * t} :=
      measurableSet_lt measurable_const continuous_norm.measurable
    have hpre : {x : Fin n → Point d |
        ‖x k‖ > S + Real.sqrt d * t} =
      Function.eval k ⁻¹'
        {x : Point d | ‖x‖ > S + Real.sqrt d * t} := rfl
    rw [hpre, measureReal_def,
      (measurePreserving_eval (fun _ : Fin n ↦ ν) k).measure_preimage
        hmeas.nullMeasurableSet]
    exact gaussianLocationMixtureLaw_radius_tail μ ϑ hϑmeas hϑS ht
  have hset : {x : Fin n → Point d |
      ∃ k, ‖x k‖ > S + Real.sqrt d * t} =
      ⋃ k : Fin n,
        {x : Fin n → Point d | ‖x k‖ > S + Real.sqrt d * t} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  change νn.real {x : Fin n → Point d |
      ∃ k, ‖x k‖ > S + Real.sqrt d * t} ≤ _
  rw [hset]
  calc
    νn.real (⋃ k : Fin n,
        {x : Fin n → Point d | ‖x k‖ > S + Real.sqrt d * t}) ≤
        ∑ k : Fin n, νn.real
          {x : Fin n → Point d | ‖x k‖ > S + Real.sqrt d * t} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin n, 2 * d * Real.exp (-t ^ 2 / 2) :=
      Finset.sum_le_sum fun k _ ↦ hcoord k
    _ = 2 * n * d * Real.exp (-t ^ 2 / 2) := by simp; ring
