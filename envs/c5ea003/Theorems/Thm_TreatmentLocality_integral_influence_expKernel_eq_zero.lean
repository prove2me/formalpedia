-- Prove2me | Theorems.Thm_TreatmentLocality_integral_influence_expKernel_eq_zero
-- name    : TreatmentLocality.integral_influence_expKernel_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:54:37.088323+00:00
-- url     : https://prove2.me/theorems/a89a5643-578d-48c1-a5d3-1f6740018396
-- title:
--   The information-sharing influence function is a martingale difference
-- statement:
--   **The influence function of the information-sharing estimator is a martingale difference.** Let $\nu$ be an invariant law of the experiment chain in which every state is visited with positive probability, and suppose the rewards are integrable. Write $\varphi_s$ for the linearisation of the model-based information-sharing estimator at the population statistics, $\varphi_s(X) = \nabla\hat\Delta(\mathbb{E}_\nu[u_{\mathrm{IS}}])[u_{\mathrm{IS}}(X)](s)$. Then for **every** step $z$,
--   $$\mathbb{E}\bigl[\varphi_s(X_{i+1}) \mid X_i = z\bigr] \;=\; 0 .$$
--
--   Three facts combine. The influence function evaluated on one observation is a difference of inverse-probability-weighted temporal-difference errors of the *plug-in* value functions. At the population statistics the plug-in value functions are the true ones — the information-sharing scheme is Fisher consistent. And the true value function makes the weighted temporal-difference error centred, by the Bellman equation. Conditioning on the past of the chain amounts to conditioning on the current state, since that is all the kernel depends on; so the conditional mean is zero pointwise, not merely almost surely.
--
--   This is the structural reason the asymptotic variance of the information-sharing estimator has no temporal-correlation term (arXiv:2407.19618, Appendix EC.3.2).
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3: Remark 1 and Proposition 5 (the model-based plug-in estimator), §6.2 (the information-sharing statistics), and Appendix EC.3.2 (the linearisation of a differentiable estimator and its asymptotic covariance, Lemma EC.4-EC.5).

import Definitions.Def_TreatmentLocalityPlugIn
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.integral_influence_expKernel_eq_zero {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (s : S) (z : Step S) :
    ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)
        ∂(expKernel M z) = 0 := by sorry
