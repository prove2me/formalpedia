-- Prove2me | Theorems.Thm_TreatmentLocality_influence_score_covariance_of_unbiased
-- name    : TreatmentLocality.influence_score_covariance_of_unbiased
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-08-22T03:24:57.477003+00:00
-- url     : https://prove2.me/theorems/348db484-c8d3-46ef-8de2-5138c268c2f2
-- title:
--   Covariance of an unbiased estimator with the accumulated influence function
-- statement:
--   **The estimator's covariance with the accumulated influence function is the information-sharing variance.** Consider the SST experiment of arXiv:2407.19618 run under the mixed policy $\pi^{1/2}$: Gaussian rewards with a known variance profile, strictly positive transitions, and a stationary law $\nu$ of a uniformly ergodic experiment chain. Let $\delta = (\delta_T)_T$ be a square-integrable estimator sequence that is unbiased for the ATE across the whole SST family (same crucial state, discount factor and reward variances; arbitrary reward means and transitions). Write
--   $$\varphi_w(X) \;=\; \sum_s w_s\, \nabla\hat\Delta_s\bigl(\mathbb{E}_\nu[u_{\mathrm{IS}}]\bigr)\bigl[u_{\mathrm{IS}}(X)\bigr]$$
--   for the linearisation of the model-based information-sharing estimator in the direction $w$, evaluated on one experiment step. The assertion is that for every horizon $T \ge 1$,
--   $$\mathbb{E}\Bigl[(w^\top \delta_T)\sum_{i=0}^{T} \varphi_w(X_i)\Bigr] \;=\; w^\top \Sigma_{\mathrm{IS}}\, w .$$
--
--   This is the Cramér-Rao pairing in the form the efficiency theorem needs. In the semiparametric picture $\varphi_w$ is the score of the SST family along the least-favourable direction $y$ — the solution of the normal equations $I_{\mathrm{step}}\,y = \nabla(w^\top\Delta)$ — so $\sum_{i \le T} \varphi_w(X_i)$ is the derivative of the log-likelihood of the observed path along $y$. Differentiating the unbiasedness identity $\mathbb{E}_{M_t}[w^\top\delta_T] = w^\top\Delta(M_t)$ at $t = 0$, and interchanging differentiation with integration, turns the left-hand side into the displayed covariance and the right-hand side into the directional derivative $\nabla(w^\top\Delta)\cdot y = y^\top I_{\mathrm{step}}\, y$, which the constrained Cramér-Rao computation of Appendix EC.4.3 identifies with $w^\top\Sigma_{\mathrm{IS}}w$.
--
--   Combined with the martingale-difference property of $\varphi_w$ along the experiment chain and the resulting identity $\mathbb{E}[\varphi_w(X_i)^2] = w^\top\Sigma_{\mathrm{IS}}w$, this display is what the information inequality is applied to, yielding the asymptotic efficiency of information sharing (Theorem 5 of arXiv:2407.19618).
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Appendix EC.4.3 (proof of Theorem 5: the constrained Cramér-Rao bound CCRB(Δ) = ∇Δᵀ CCRB(θ) ∇Δ = Σ_IS), with Appendix EC.8.3, Lemma EC.8 (Stoica and Ng 1998, Theorem 1) and Lemma EC.9 (Moore 2010, Corollary 3.10).

import Definitions.Def_TreatmentLocalityEstimator
import Definitions.Def_MarkovErgodicity
import Mathlib.Probability.Martingale.Basic

open MeasureTheory ProbabilityTheory Filter TreatmentLocality
open scoped NNReal ENNReal Topology

theorem TreatmentLocality.influence_score_covariance_of_unbiased {S : Type*} [Fintype S]
    [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (huni : MarkovChainCLT.UniformlyErgodic (expKernel M) ν)
    (δ : (T : ℕ) → (Fin T → Step S) → S → ℝ)
    (hmeas : ∀ T s, Measurable (fun path => δ T path s))
    (hL2 : ∀ T s, MemLp (fun ω : ℕ → Step S => δ T (fun i => ω (i.1 + 1)) s) 2
      (MarkovChainCLT.chainMeasure (expKernel M) ν))
    (hunbiased : ∀ (M' : Model S), M'.crucial = M.crucial → M'.γdisc = M.γdisc →
      (∃ m' : S → Bool → ℝ, M'.GaussianRewards m' v) →
      ∀ (ν' : Measure (Step S)) (_ : IsProbabilityMeasure ν'),
        Kernel.Invariant (expKernel M') ν' →
        MarkovChainCLT.UniformlyErgodic (expKernel M') ν' →
        ∀ T : ℕ, 1 ≤ T → ∀ s,
          ∫ ω, δ T (fun i => ω (i.1 + 1)) s
            ∂(MarkovChainCLT.chainMeasure (expKernel M') ν') = M'.ate s)
    (w : S → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    ∫ ω, (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s)
          * (∑ i ∈ Finset.range (T + 1),
              ∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
                (estObs M .IS (ω i)))
        ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
      = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' := by sorry
