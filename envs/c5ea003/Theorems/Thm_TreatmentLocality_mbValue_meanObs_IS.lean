-- Prove2me | Theorems.Thm_TreatmentLocality_mbValue_meanObs_IS
-- name    : TreatmentLocality.mbValue_meanObs_IS
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T01:58:39.088174+00:00
-- url     : https://prove2.me/theorems/3cd0d33c-29be-4f10-9c5a-1f102af340fe
-- title:
--   Fisher consistency of the model-based information-sharing estimator
-- statement:
--   **Fisher consistency of the model-based information-sharing estimator.** Let $\nu$ be an invariant law of the experiment chain in which every state is visited with positive probability, and suppose the rewards have a first moment. Then at the *population* statistics of the information-sharing scheme the plug-in value function is exactly the true one:
--   $$\hat V^a\bigl(\mathbb{E}_\nu[K_{\mathrm{IS}}], \mathbb{E}_\nu[R_{\mathrm{IS}}]\bigr) \;=\; V^a \;=\; (I - \gamma P^a)^{-1} r^a .$$
--
--   Both the expected counts and the expected reward statistics equal the stationary visit probability $\mu(i)$ times the corresponding true quantity, so the visit probabilities cancel in the normalisation: the plug-in transition matrix is $P^a$ and the plug-in mean rewards are $r^a$. Consequently the model-based estimator of the ATE is Fisher consistent, $\hat\Delta = V^t - V^c = \Delta$ at the population statistics.
--
--   This is what makes the linearisation of the estimator a *centred* statistic: because the plug-in value function at the population point is the true value function, the temporal-difference residual $r + \gamma V^a(s') - V^a(s)$ appearing in its gradient has conditional mean zero given the current state, by the Bellman equation. That centring is what turns the influence function of the information-sharing estimator into a martingale difference sequence along the experiment chain (arXiv:2407.19618, Remark 1, Proposition 5 and Appendix EC.3.2).
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3: §3 Algorithm 1 (the mixed policy π^{1/2} and the experiment trajectory), §6.2 (the information-sharing statistics K^a_IS, R^a_IS and their limits Diag(μ^{1/2})P^a and Diag(μ^{1/2})r^a), Remark 1 and Proposition 5 (the model-based plug-in estimator), and Appendix EC.3.1-EC.3.2.

import Definitions.Def_TreatmentLocalityPlugIn
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.mbValue_meanObs_IS {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) :
    mbValue M (meanObs M .IS ν) a = M.value a := by sorry
