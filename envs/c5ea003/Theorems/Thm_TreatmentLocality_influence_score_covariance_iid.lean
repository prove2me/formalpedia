-- Prove2me | Theorems.Thm_TreatmentLocality_influence_score_covariance_iid
-- name    : TreatmentLocality.influence_score_covariance_iid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T15:19:14.397822+00:00
-- url     : https://prove2.me/theorems/7431639e-0640-4583-ba53-efcbfe7aecdd
-- title:
--   Covariance of an unbiased estimator with the accumulated score
-- statement:
--   **The estimator's covariance with the accumulated score is the information-sharing variance.** In the setting of Theorem 5 of arXiv:2407.19618 — the SST experiment observed as $T$ i.i.d. draws, and an estimator sequence unbiased for the ATE across the family — write
--   $$\varphi_w(X) \;=\; \sum_s w_s\, \nabla\hat\Delta_s\bigl(\mathbb E[u_{\mathrm{IS}}]\bigr)\bigl[u_{\mathrm{IS}}(X)\bigr]$$
--   for the linearisation of the model-based information-sharing estimator in the direction $w$, evaluated on one observation. Then for every $T \ge 1$,
--   $$\mathbb E\Bigl[(w^\top\delta_T)\sum_{i=1}^{T}\varphi_w(X_i)\Bigr] \;=\; w^\top\Sigma_{\mathrm{IS}}\,w .$$
--
--   This is the Cramér-Rao pairing. The influence function $\varphi_w$ is a score direction of the SST family, so $\sum_i \varphi_w(X_i)$ is the derivative of the log-likelihood of the sample along the corresponding curve of models. Differentiating the unbiasedness identity $\mathbb E_{M_t}[w^\top\delta_T] = w^\top\Delta(M_t)$ at $t = 0$ turns the left-hand side into the displayed covariance and the right-hand side into the directional derivative of the ATE, which the computation of Appendix EC.4.3 identifies with $w^\top\Sigma_{\mathrm{IS}}w$.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Theorem 5 and Appendix EC.4.3.

import Definitions.Def_TreatmentLocalityIID
import Definitions.Def_TreatmentLocalityEstimator
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.influence_score_covariance_iid {S : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (δ : (T : ℕ) → (Fin T → Step S) → S → ℝ)
    (hmeas : ∀ T s, Measurable (fun path => δ T path s))
    (hL2 : ∀ T s, MemLp (fun path => δ T path s) 2
      (sampleLaw M (Measure.map Step.state ν) T))
    (hunbiased : ∀ (M' : Model S), M'.crucial = M.crucial → M'.γdisc = M.γdisc →
      (∃ m' : S → Bool → ℝ, M'.GaussianRewards m' v) →
      ∀ T : ℕ, 1 ≤ T → ∀ s,
        ∫ path, δ T path s ∂(sampleLaw M' (Measure.map Step.state ν) T) = M'.ate s)
    (w : S → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    ∫ path, (∑ s, w s * δ T path s)
        * (∑ i : Fin T, ∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s)
            (meanObs M .IS ν) (estObs M .IS (path i)))
        ∂(sampleLaw M (Measure.map Step.state ν) T)
      = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' := by sorry
