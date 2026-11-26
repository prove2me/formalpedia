-- Prove2me | solution 1 for ReweightedNPMLE.gaussianLocationMixtureLaw_injective
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:12:37.982625+00:00
-- url     : https://prove2.me/submissions/cd86ad41-50cf-4703-b833-21eea78d478e

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Theorems.Thm_ReweightedNPMLE_gaussianLocationMixtureLaw_id_eq_convolution

/-!
# Identifiability of Gaussian location mixtures

Convolution with a standard Gaussian is injective on probability measures:
its characteristic function is nowhere zero.  Combined with the generative-
law/density identity, this proves identifiability of the mixing law from the
mixture density.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Convolution with a standard Gaussian determines the location law. -/
theorem solution
    {d : ℕ} (μ ν : Measure (Point d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : gaussianLocationMixtureLaw μ id =
      gaussianLocationMixtureLaw ν id) : μ = ν := by
  rw [gaussianLocationMixtureLaw_id_eq_convolution μ,
    gaussianLocationMixtureLaw_id_eq_convolution ν] at h
  have hchar := congrArg charFun h
  rw [charFun_map_add_prod_eq_mul, charFun_map_add_prod_eq_mul] at hchar
  apply Measure.ext_of_charFun
  funext t
  have ht := congrFun hchar t
  simp only [Pi.mul_apply] at ht
  exact mul_right_cancel₀ (by
    rw [charFun_stdGaussian]
    exact Complex.exp_ne_zero _) ht
