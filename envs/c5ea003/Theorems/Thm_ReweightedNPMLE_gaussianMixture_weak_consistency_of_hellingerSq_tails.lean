-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianMixture_weak_consistency_of_hellingerSq_tails
-- name    : ReweightedNPMLE.gaussianMixture_weak_consistency_of_hellingerSq_tails
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:48:34.163243+00:00
-- url     : https://prove2.me/theorems/4f620e55-7d5b-5c68-8985-7e961a11c77a
-- title:
--   Weak mixing-law consistency from Hellinger tails in varying experiments
-- statement:
--   Let $d\ge0$ be an integer and let $K\subseteq\mathbb R^d$ be compact. For a Borel probability measure $G$ on $K$, write
--   $$
--   f_G(x)=\int_K\varphi_d(x-\theta)\,dG(\theta),\qquad
--   h^2(f,g)=\int_{\mathbb R^d}(\sqrt f-\sqrt g)^2\,dx,
--   $$
--   where $\varphi_d$ is the standard Gaussian density. Probability measures on $K$ carry the weak topology.
--
--   Fix $G_\star\in\mathcal P(K)$. For each integer $n\ge0$, let $(\Omega_n,\mathcal F_n,\mu_n)$ be a finite measure space and let $\widehat G_n:\Omega_n\to\mathcal P(K)$ be any map. Assume that for every $\delta>0$,
--   $$
--   \mu_n^*\{\omega:h^2(f_{\widehat G_n(\omega)},f_{G_\star})\ge\delta\}
--   \longrightarrow0.
--   $$
--   Then, for every weak neighborhood $U$ of $G_\star$,
--   $$
--   \mu_n^*\{\omega:\widehat G_n(\omega)\notin U\}\longrightarrow0.
--   $$
--   Here $\mu_n^*$ denotes the outer measure induced by $\mu_n$. The formal statement does not require measurability of the maps or their deviation events. For measurable estimators under probability measures, these quantities are ordinary probabilities, and the conclusion is weak consistency in probability.
--
--   The result permits the sample space to vary with sample size, as in a sequence of Gaussian-mixture data experiments.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianIdentifiability.lean#L362-L391

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

theorem ReweightedNPMLE.gaussianMixture_weak_consistency_of_hellingerSq_tails
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
      Tendsto (fun n ↦ (μ n).real {ω | Ghat n ω ∉ U}) atTop (𝓝 0) := by sorry
