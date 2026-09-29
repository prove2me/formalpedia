-- Prove2me | Theorems.Thm_TreatmentLocality_meanObs_IS_rwd
-- name    : TreatmentLocality.meanObs_IS_rwd
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T01:58:33.862167+00:00
-- url     : https://prove2.me/theorems/ca8109e6-ce54-47ae-a384-450258ce5041
-- title:
--   Population reward statistic of information sharing: $\mu(i)r^a(i)$
-- statement:
--   **The population reward statistic of the information-sharing scheme.** Under an invariant law $\nu$ of the experiment chain, with rewards having a first moment,
--   $$\mathbb{E}_\nu\bigl[R^a_{\mathrm{IS}}(i)\bigr] \;=\; \mu(i)\, r^a(i),\qquad \mu(i) = \mathbb{P}_\nu[s = i],$$
--   the stationary visit probability of $i$ times the true arm-$a$ mean reward. The mechanism is the same as for the transition counts: the inverse-probability weight $2\cdot\mathbf 1[\gamma=a]$ at the crucial state cancels against the fair coin, and away from the crucial state the two arms agree, so the shared sample with weight $1$ reports the arm-$a$ mean reward (arXiv:2407.19618, §6.2).
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

theorem TreatmentLocality.meanObs_IS_rwd {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν) (a : Bool) (i : S) :
    (meanObs M .IS ν a).2 i
      = (∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν) * M.polReward a i := by sorry
