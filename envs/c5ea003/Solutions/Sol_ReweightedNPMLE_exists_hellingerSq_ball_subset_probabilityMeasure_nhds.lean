-- Prove2me | solution 1 for ReweightedNPMLE.exists_hellingerSq_ball_subset_probabilityMeasure_nhds
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:15:21.216351+00:00
-- url     : https://prove2.me/submissions/64561c88-2a10-41cb-80ef-f0ab13d7544b

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
import Theorems.Thm_ReweightedNPMLE_tendsto_probabilityMeasure_of_tendsto_gaussianMixture_hellingerSq_zero

-- Inline helpers preserved from ReweightedNPMLE.Hellinger.
section
/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE















theorem hellingerSq_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : 0 ≤ hellingerSq μ p q := by
  apply integral_nonneg
  intro x
  exact sq_nonneg _









































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
/-- Uniform topological inverse at the true mixing law: every weak
neighborhood contains a sufficiently small squared-Hellinger ball of
Gaussian-mixture densities.  Compactness and identifiability are essential. -/
theorem solution
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    (Gstar : ProbabilityMeasure K) {U : Set (ProbabilityMeasure K)}
    (hU : U ∈ 𝓝 Gstar) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : ProbabilityMeasure K,
      hellingerSq volume
          (gaussianMixture (G : Measure K) (fun θ : K ↦ (θ : Point d)))
          (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))) < δ →
        G ∈ U := by
  classical
  by_contra hcontra
  push_neg at hcontra
  have hchoice : ∀ n : ℕ, ∃ G : ProbabilityMeasure K,
      hellingerSq volume
          (gaussianMixture (G : Measure K) (fun θ : K ↦ (θ : Point d)))
          (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))) <
        1 / ((n : ℝ) + 1) ∧ G ∉ U := by
    intro n
    exact hcontra (1 / ((n : ℝ) + 1)) (by positivity)
  choose Gs hsmall hout using hchoice
  have hhell : Tendsto (fun n ↦ hellingerSq volume
        (gaussianMixture (Gs n : Measure K) (fun θ : K ↦ (θ : Point d)))
        (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))))
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact hellingerSq_nonneg volume _ _
    · intro n
      exact (hsmall n).le
    · simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hGs :=
    tendsto_probabilityMeasure_of_tendsto_gaussianMixture_hellingerSq_zero
      hKcompact Gs Gstar hhell
  have hboth : ∀ᶠ n in atTop, Gs n ∈ U ∧ Gs n ∉ U := by
    filter_upwards [hGs hU] with n hn
    exact ⟨hn, hout n⟩
  rcases hboth.exists with ⟨n, hn, hnout⟩
  exact hnout hn
