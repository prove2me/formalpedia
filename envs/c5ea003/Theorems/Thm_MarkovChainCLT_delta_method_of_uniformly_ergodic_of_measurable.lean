-- Prove2me | Theorems.Thm_MarkovChainCLT_delta_method_of_uniformly_ergodic_of_measurable
-- name    : MarkovChainCLT.delta_method_of_uniformly_ergodic_of_measurable
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-21T17:40:42.599968+00:00
-- url     : https://prove2.me/theorems/13623a1c-f963-457d-bf58-ceb9cd2a01d1
-- title:
--   Delta method for Markov chain statistics (Lemma EC.5), measurable estimator
-- statement:
--   **Lemma EC.5 of arXiv:2407.19618 (linearization / delta method for Markov chain statistics), with the estimator required to be measurable.**
--
--   Let $\{X_i\}$ be a uniformly ergodic Harris chain on $\mathsf X$ with stationary distribution $\pi$, and let $u:\mathsf X\to\mathbb R^{\iota}$ be a vector of square-integrable statistics over a finite index set $\iota$. Write
--   $$\bar u_n \;=\; \frac1n\sum_{i=1}^n u(X_i),\qquad \mu \;=\; \mathbb E_\pi[u(X_1)] .$$
--   Let $\varphi:\mathbb R^\iota\to\mathbb R$ be Fréchet-differentiable at $\mu$ with derivative $\varphi'$. Then
--   $$\sqrt n\,\big(\varphi(\bar u_n)-\varphi(\mu)\big)\;\xrightarrow{\ d\ }\;N\!\big(0,\;\sigma^2(\varphi'\circ u)\big),$$
--   where $\sigma^2(\cdot)$ is the Markov chain asymptotic variance — the variance of the sample average of the **linearized observable** $x\mapsto \varphi'(u(x))$, i.e. $\nabla\varphi^\top\Sigma_u\nabla\varphi$ in the notation of the paper.
--
--   **Why the extra hypothesis.** The conclusion asserts convergence in distribution, and in Mathlib that carries an almost-everywhere measurability obligation on each $\omega\mapsto\varphi(\bar u_n(\omega))$. Differentiability of $\varphi$ at the single point $\mu$ does not supply it: a function of the form $\varphi(v)=\|v-\mu\|^2\mathbf 1_A(v)$ with $A$ non-measurable is Fréchet-differentiable at $\mu$ with derivative $0$ and is not measurable anywhere else. This statement therefore carries `Measurable g` explicitly. The paper is on the right side of this already — Definition 1 speaks of *differentiable* estimators and Appendix EC.3.2 uses "$f$ is differentiable (and thus continuous)" — so the hypothesis costs nothing in the intended application, where the estimator is a genuinely differentiable, hence continuous, hence measurable, function of the statistics.
--
--   **What drives the proof.** Because $\iota$ is finite, $\varphi'$ is a finite linear combination of coordinates, so $\varphi'(\bar u_n)$ *is* the sample average of the scalar observable $\varphi'\circ u$ and inherits the Markov chain central limit theorem directly. The difference between the two sequences is $\sqrt n$ times the first-order remainder of $\varphi$ at $\mu$, and it vanishes in probability because the scaled deviations $\sqrt n(\bar u_n-\mu)$ are tight — uniform ergodicity gives a second-moment bound uniform in $n$ — so a Slutsky-type argument transfers the limit law. This is Step 2 of Appendix EC.3.1 combined with Lemma EC.5.
-- source:
--   Chen, Simchi-Levi, Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, https://arxiv.org/abs/2407.19618, Appendix EC.3.1 Step 2 (delta method) and Appendix EC.8, Lemma EC.5 (linearization, adapted from Farias et al. 2022, Lemma 6). Differs from MarkovChainCLT.delta_method_of_uniformly_ergodic only by the added hypothesis that the estimator g is measurable, which the convergence-in-distribution conclusion requires and which differentiability at a single point does not supply; the paper's Definition 1 and Appendix EC.3.2 both treat f as differentiable, hence continuous, hence measurable.

import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem MarkovChainCLT.delta_method_of_uniformly_ergodic_of_measurable {X : Type*}
    [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π)
    (huni : MarkovChainCLT.UniformlyErgodic P π)
    {ι : Type*} [Fintype ι]
    (u : X → ι → ℝ) (hu : ∀ p, Measurable (fun x => u x p))
    (hL2 : ∀ p, MemLp (fun x => u x p) 2 π)
    (g : (ι → ℝ) → ℝ) (hgm : Measurable g) (g' : (ι → ℝ) →L[ℝ] ℝ)
    (hg : HasFDerivAt g g' (fun p => ∫ x, u x p ∂π)) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) =>
        Real.sqrt n * (g (fun p => MarkovChainCLT.sampleAvg (fun x => u x p) n ω)
          - g (fun p => ∫ x, u x p ∂π)))
      atTop (id : ℝ → ℝ) (fun _ => MarkovChainCLT.chainMeasure P π)
      (gaussianReal 0
        (MarkovChainCLT.asymptoticVariance P π (fun x => g' (u x))).toNNReal) := by sorry
