-- Prove2me | Theorems.Thm_TreatmentLocality_obsLaw_map_state
-- name    : TreatmentLocality.obsLaw_map_state
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T15:19:18.701442+00:00
-- url     : https://prove2.me/theorems/cc74c3d5-2e21-4165-8e20-e1c74dbc70c2
-- title:
--   An invariant law is the observation law of its state marginal
-- statement:
--   **An invariant law of the experiment chain is the observation law of its own state marginal.** Let $\nu$ be an invariant probability law of the experiment chain of arXiv:2407.19618 on the space of one step $(s,\gamma,s',r)$, and let $\mu$ be the law of its current state. Then $\nu$ is exactly the law obtained by drawing a state from $\mu$ and taking one step of the mixed policy $\pi^{1/2}$ from it.
--
--   This is the fact that licenses the i.i.d. reading of the stationary experiment: a single stationary observation *is* a draw from the fixed state marginal followed by one step, so a sample of $T$ such observations, taken independently, has the product of that law. Two ingredients: the transition kernel of the chain produces the new step by taking one step from the previous step's *next* state, and invariance makes the current state and the next state identically distributed.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Section 3 (Algorithm 1) and Appendix EC.4.3.

import Definitions.Def_TreatmentLocalityIID
import Definitions.Def_TreatmentLocalityEstimator
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.obsLaw_map_state {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) :
    obsLaw M (Measure.map Step.state ν) = ν := by sorry
