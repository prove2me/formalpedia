-- Prove2me | solution 1 for ReweightedNPMLE.gaussianProduct_max_coordinate_tail
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:08:17.237865+00:00
-- url     : https://prove2.me/submissions/f0597cbe-f4f2-492b-a7bf-4b8c39240496

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
import Theorems.Thm_ReweightedNPMLE_gaussianReal_two_sided_tail

/-!
# Gaussian radius bounds

Chernoff and finite-union estimates for the radius event in the likelihood-net
argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- A union bound for the largest coordinate of a standard Gaussian product. -/
theorem solution (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)).real
        {z : Fin d → ℝ | ∃ i, |z i| > t} ≤
      2 * d * Real.exp (-t ^ 2 / 2) := by
  let μd : Measure (Fin d → ℝ) :=
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)
  have hcoord (i : Fin d) :
      μd.real {z : Fin d → ℝ | |z i| > t} ≤
        2 * Real.exp (-t ^ 2 / 2) := by
    have hmeas : MeasurableSet {x : ℝ | |x| > t} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    have hpre : {z : Fin d → ℝ | |z i| > t} =
        Function.eval i ⁻¹' {x : ℝ | |x| > t} := rfl
    rw [hpre, measureReal_def,
      (measurePreserving_eval (fun _ : Fin d ↦ gaussianReal 0 1) i).measure_preimage
        hmeas.nullMeasurableSet]
    exact gaussianReal_two_sided_tail ht
  have hset : {z : Fin d → ℝ | ∃ i, |z i| > t} =
      ⋃ i : Fin d, {z : Fin d → ℝ | |z i| > t} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  change μd.real {z : Fin d → ℝ | ∃ i, |z i| > t} ≤ _
  rw [hset]
  calc
    μd.real (⋃ i : Fin d, {z : Fin d → ℝ | |z i| > t}) ≤
        ∑ i : Fin d, μd.real {z : Fin d → ℝ | |z i| > t} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin d, 2 * Real.exp (-t ^ 2 / 2) :=
      Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = 2 * d * Real.exp (-t ^ 2 / 2) := by simp; ring
