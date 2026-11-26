-- Prove2me | Theorems.Thm_ReweightedNPMLE_tendsto_probabilityMeasure_of_tendsto_gaussianMixture_hellingerSq_zero
-- name    : ReweightedNPMLE.tendsto_probabilityMeasure_of_tendsto_gaussianMixture_hellingerSq_zero
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:48:00.698864+00:00
-- url     : https://prove2.me/theorems/10f3e1ee-2196-5759-9e9e-8f52df7f2f0e
-- title:
--   Hellinger convergence of Gaussian mixtures implies weak convergence of mixing laws
-- statement:
--   Let $d\ge0$ be an integer and let $K\subseteq\mathbb R^d$ be compact. For a Borel probability measure $G$ on $K$, write
--   $$
--   f_G(x)=\int_K\varphi_d(x-\theta)\,dG(\theta),\qquad
--   h^2(f,g)=\int_{\mathbb R^d}(\sqrt f-\sqrt g)^2\,dx,
--   $$
--   where $\varphi_d$ is the standard Gaussian density. Probability measures on $K$ carry the weak topology.
--
--   For any sequence $(G_n)$ of probability measures on $K$ and any probability measure $G_\star$ on $K$,
--   $$
--   h^2(f_{G_n},f_{G_\star})\longrightarrow0
--   \quad\Longrightarrow\quad
--   G_n\Rightarrow G_\star.
--   $$
--
--   This is the consistency bridge from estimating the mixture density to recovering the mixing distribution itself. Compactness controls possible mixing-law limits, and Gaussian identifiability ensures that the limit is unique.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianIdentifiability.lean#L144-L293

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

theorem ReweightedNPMLE.tendsto_probabilityMeasure_of_tendsto_gaussianMixture_hellingerSq_zero
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    (Gs : ℕ → ProbabilityMeasure K) (Gstar : ProbabilityMeasure K)
    (hhell : Tendsto (fun n ↦ hellingerSq volume
        (gaussianMixture (Gs n : Measure K) (fun θ : K ↦ (θ : Point d)))
        (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))))
      atTop (𝓝 0)) :
    Tendsto Gs atTop (𝓝 Gstar) := by sorry
