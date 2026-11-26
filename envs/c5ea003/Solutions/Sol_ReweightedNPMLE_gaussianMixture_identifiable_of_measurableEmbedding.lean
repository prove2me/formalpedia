-- Prove2me | solution 1 for ReweightedNPMLE.gaussianMixture_identifiable_of_measurableEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:13:23.088217+00:00
-- url     : https://prove2.me/submissions/f3b581b5-d2ac-4f9e-8e52-8234247b8474

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
import Theorems.Thm_ReweightedNPMLE_gaussianLocationMixtureLaw_injective

-- Inline helpers preserved from ReweightedNPMLE.GaussianIdentifiability.
section
/-!
# Identifiability of Gaussian location mixtures

Convolution with a standard Gaussian is injective on probability measures:
its characteristic function is nowhere zero.  Combined with the generative-
law/density identity, this proves identifiability of the mixing law from the
mixture density.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

namespace ReweightedNPMLE







/-- Two probability mixing laws with almost-everywhere equal Gaussian
location-mixture densities are equal. -/
theorem gaussianMixture_identifiable_of_ae_eq
    {d : ℕ} (μ ν : Measure (Point d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : gaussianMixture μ id =ᵐ[volume] gaussianMixture ν id) : μ = ν := by
  apply gaussianLocationMixtureLaw_injective μ ν
  rw [gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture
      μ id measurable_id,
    gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture
      ν id measurable_id]
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  rw [hx]















end ReweightedNPMLE
end

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
/-- Identifiability is invariant under a measurable embedding of the mixing
parameter space into Euclidean location space. -/
theorem solution
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : Measure Θ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (θ : Θ → Point d) (hθ : MeasurableEmbedding θ)
    (h : gaussianMixture μ θ =ᵐ[volume] gaussianMixture ν θ) : μ = ν := by
  have hdensity (ρ : Measure Θ) [IsProbabilityMeasure ρ] :
      gaussianMixture (ρ.map θ) id = gaussianMixture ρ θ := by
    funext x
    unfold gaussianMixture
    rw [hθ.integral_map]
    rfl
  letI : IsProbabilityMeasure (μ.map θ) :=
    Measure.isProbabilityMeasure_map hθ.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.map θ) :=
    Measure.isProbabilityMeasure_map hθ.measurable.aemeasurable
  have hmap : μ.map θ = ν.map θ := by
    apply gaussianMixture_identifiable_of_ae_eq
    rw [hdensity μ, hdensity ν]
    exact h
  exact hθ.map_injective hmap
