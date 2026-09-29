-- Prove2me | Theorems.Thm_TreatmentLocality_asymptotic_efficiency_of_information_sharing_iid
-- name    : TreatmentLocality.asymptotic_efficiency_of_information_sharing_iid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T15:19:09.630767+00:00
-- url     : https://prove2.me/theorems/8458e468-c596-462e-8f92-0f5f687c72f2
-- title:
--   Theorem 5 — asymptotic efficiency of information sharing
-- statement:
--   **Asymptotic efficiency of information sharing.** Consider the SST experiment of arXiv:2407.19618 run under the mixed policy $\pi^{1/2}$ from its stationary state distribution $\mu$, so that the observations $X_1,\dots,X_T$ are i.i.d. draws of one experiment step. Let $\delta = (\delta_T)_T$ be a square-integrable estimator sequence that is unbiased for the average treatment effect across the whole SST family — same crucial state, discount factor and reward variances, arbitrary reward means and transitions. Then for every direction $w$ and every horizon $T \ge 1$,
--   $$w^\top \Sigma_{\mathrm{IS}}\, w \;\le\; T\;\operatorname{Var}\bigl[w^\top\delta_T\bigr].$$
--
--   In words: no unbiased estimator can beat the information-sharing estimator asymptotically. $\Sigma_{\mathrm{IS}}$ is the asymptotic covariance of the model-based information-sharing estimator, so the left-hand side is the variance that scheme achieves in the direction $w$, while the right-hand side is $T$ times the finite-sample variance of any competitor — the quantity that converges to its asymptotic variance. The bound is the Cramér-Rao inequality for the SST family, with the constraint that transition rows are probability vectors handled by restricting to centred perturbations rather than by inverting a singular Fisher matrix.
--
--   *Formalization note.* Unbiasedness is required across the family because a Cramér-Rao bound constrains an estimator only through how its bias varies with the parameter; the hypothesis fixes the reward variance profile, matching the paper's parametrisation.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Theorem 5 and Appendix EC.4.3.

import Definitions.Def_TreatmentLocalityIID
import Definitions.Def_TreatmentLocalityEstimator
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.asymptotic_efficiency_of_information_sharing_iid {S : Type*} [Fintype S] [DecidableEq S]
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
        ∫ path, δ T path s ∂(sampleLaw M' (Measure.map Step.state ν) T) = M'.ate s) :
    ∀ (w : S → ℝ) (T : ℕ), 1 ≤ T →
      ∑ s, ∑ s', w s * mbISCov M ν s s' * w s'
        ≤ (T : ℝ) * ∫ path, (∑ s, w s * δ T path s
              - ∫ path', ∑ s, w s * δ T path' s
                  ∂(sampleLaw M (Measure.map Step.state ν) T)) ^ 2
            ∂(sampleLaw M (Measure.map Step.state ν) T) := by sorry
