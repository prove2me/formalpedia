-- Prove2me | solution 1 for ReweightedNPMLE.gaussianMixture_weak_consistency_of_hellingerSq_tails
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:16:12.417817+00:00
-- url     : https://prove2.me/submissions/82530e67-92e8-46bb-a5f3-8e5acdeb2939

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
import Theorems.Thm_ReweightedNPMLE_exists_hellingerSq_ball_subset_probabilityMeasure_nhds

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
/-- Weak consistency in probability for a triangular sequence of experiments.
The sample space may vary with `n` (as it does for `Fin n → Point d`).  The
conclusion is expressed intrinsically: the probability of leaving any weak
neighborhood of `Gstar` tends to zero. -/
theorem solution
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    (Gstar : ProbabilityMeasure K)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (Ghat : ∀ n, Ω n → ProbabilityMeasure K)
    (hhell : ∀ δ : ℝ, 0 < δ → Tendsto (fun n ↦ (μ n).real
      {ω | δ ≤ hellingerSq volume
        (gaussianMixture (Ghat n ω : Measure K) (fun θ : K ↦ (θ : Point d)))
        (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d)))})
      atTop (𝓝 0)) :
    ∀ U ∈ 𝓝 Gstar,
      Tendsto (fun n ↦ (μ n).real {ω | Ghat n ω ∉ U}) atTop (𝓝 0) := by
  intro U hU
  obtain ⟨δ, hδ, hδU⟩ :=
    exists_hellingerSq_ball_subset_probabilityMeasure_nhds
      hKcompact Gstar hU
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) (hhell δ hδ)
  ·
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change Ghat n ω ∉ U at hω
    change δ ≤ hellingerSq volume
      (gaussianMixture (Ghat n ω : Measure K) (fun θ : K ↦ (θ : Point d)))
      (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d)))
    exact not_lt.mp (fun hlt ↦ hω (hδU (Ghat n ω) hlt))
