-- Prove2me | Theorems.Thm_TreatmentLocality_meanObs_IS_trans
-- name    : TreatmentLocality.meanObs_IS_trans
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T01:58:22.736314+00:00
-- url     : https://prove2.me/theorems/2f239442-027f-4384-9b96-0b55d8141f38
-- title:
--   Population transition statistic of information sharing: $\mu(i)P^a(i,j)$
-- statement:
--   **The population transition statistic of the information-sharing scheme.** Under an invariant law $\nu$ of the experiment chain, the expected information-sharing count of the transition $i \to j$ under arm $a$ is
--   $$\mathbb{E}_\nu\bigl[K^a_{\mathrm{IS}}(i,j)\bigr] \;=\; \mu(i)\, P^a(i,j),\qquad \mu(i) = \mathbb{P}_\nu[s = i],$$
--   the stationary visit probability of $i$ times the true arm-$a$ transition probability.
--
--   This is the precise sense in which information sharing is unbiased. At the crucial state the statistic carries the inverse-probability weight $2\cdot\mathbf 1[\gamma = a]$, and the factor $2$ cancels exactly against the fair coin of the mixed policy; away from the crucial state the two arms execute the same action, so the sample may be shared with weight $1$ and still reports the arm-$a$ transition. Both cases produce the same answer, which is why the two arms' estimates can be pooled off the crucial state without bias (arXiv:2407.19618, §6.2).
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

theorem TreatmentLocality.meanObs_IS_trans {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (a : Bool) (i j : S) :
    (meanObs M .IS ν a).1 i j
      = (∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν) * M.polTrans a i j := by sorry
