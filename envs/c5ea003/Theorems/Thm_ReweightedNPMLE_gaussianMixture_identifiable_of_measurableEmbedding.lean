-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianMixture_identifiable_of_measurableEmbedding
-- name    : ReweightedNPMLE.gaussianMixture_identifiable_of_measurableEmbedding
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:47:40.427244+00:00
-- url     : https://prove2.me/theorems/44188839-7b5c-4f2a-b0e2-732dc56cb88b
-- title:
--   Gaussian mixture identifiability under measurable parameter embeddings
-- statement:
--   Let $d\ge0$ be an integer, let $\Theta$ be a measurable space, and let $\theta:\Theta\to\mathbb R^d$ be a measurable embedding. Let $\mu,\nu$ be probability measures on $\Theta$, and define
--   $$
--   f_\rho(x)=\int_\Theta\varphi_d(x-\theta(a))\,d\rho(a)
--   \qquad(\rho\in\{\mu,\nu\}),
--   $$
--   where $\varphi_d$ is the standard Gaussian density. Then
--   $$
--   f_\mu=f_\nu\quad\text{Lebesgue-almost everywhere}
--   \quad\Longrightarrow\quad\mu=\nu.
--   $$
--   Compactness and continuity of the parameterization are not required; the hypothesis is the measurable-embedding property.
--
--   This transports Gaussian identifiability from Euclidean location measures to an abstract parameter space without losing the identity of its mixing laws.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianIdentifiability.lean#L99-L120

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

/-!
# Identifiability of Gaussian location mixtures

Convolution with a standard Gaussian is injective on probability measures:
its characteristic function is nowhere zero.  Combined with the generative-
law/density identity, this proves identifiability of the mixing law from the
mixture density.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

open ReweightedNPMLE

theorem ReweightedNPMLE.gaussianMixture_identifiable_of_measurableEmbedding
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : Measure Θ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (θ : Θ → Point d) (hθ : MeasurableEmbedding θ)
    (h : gaussianMixture μ θ =ᵐ[volume] gaussianMixture ν θ) : μ = ν := by sorry
