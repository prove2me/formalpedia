-- Prove2me | Theorems.Thm_ReweightedNPMLE_exists_hellingerSq_ball_subset_probabilityMeasure_nhds
-- name    : ReweightedNPMLE.exists_hellingerSq_ball_subset_probabilityMeasure_nhds
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:48:18.698867+00:00
-- url     : https://prove2.me/theorems/b76ce25f-0801-57fa-a422-d1178bd5c0f9
-- title:
--   Small Gaussian-mixture Hellinger balls lie in weak neighborhoods
-- statement:
--   Let $d\ge0$ be an integer and let $K\subseteq\mathbb R^d$ be compact. For a Borel probability measure $G$ on $K$, write
--   $$
--   f_G(x)=\int_K\varphi_d(x-\theta)\,dG(\theta),\qquad
--   h^2(f,g)=\int_{\mathbb R^d}(\sqrt f-\sqrt g)^2\,dx,
--   $$
--   where $\varphi_d$ is the standard Gaussian density. Probability measures on $K$ carry the weak topology.
--
--   Fix a probability measure $G_\star$ on $K$ and a weak neighborhood $U$ of $G_\star$; $U$ need not itself be open. Then there exists $\delta>0$ such that
--   $$
--   \{G\in\mathcal P(K):h^2(f_G,f_{G_\star})<\delta\}\subseteq U.
--   $$
--
--   The radius works uniformly over every mixing law $G$ on $K$. This local inverse-continuity statement converts density-distance tail bounds into departures from arbitrary weak neighborhoods.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianIdentifiability.lean#L295-L336

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

theorem ReweightedNPMLE.exists_hellingerSq_ball_subset_probabilityMeasure_nhds
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    (Gstar : ProbabilityMeasure K) {U : Set (ProbabilityMeasure K)}
    (hU : U ∈ 𝓝 Gstar) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : ProbabilityMeasure K,
      hellingerSq volume
          (gaussianMixture (G : Measure K) (fun θ : K ↦ (θ : Point d)))
          (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))) < δ →
        G ∈ U := by sorry
