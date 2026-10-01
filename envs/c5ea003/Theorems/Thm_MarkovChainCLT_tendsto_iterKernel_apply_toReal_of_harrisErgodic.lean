-- Prove2me | Theorems.Thm_MarkovChainCLT_tendsto_iterKernel_apply_toReal_of_harrisErgodic
-- name    : MarkovChainCLT.tendsto_iterKernel_apply_toReal_of_harrisErgodic
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-04T20:10:45.792989+00:00
-- url     : https://prove2.me/theorems/802ed505-c4fa-4c1f-a95e-70de64cc9836
-- title:
--   Harris ergodicity gives pointwise convergence $P^n(x,A) \to \pi(A)$
-- statement:
--   Let $P$ be a Markov kernel on a state space $\mathsf{X}$ with invariant probability distribution $\pi$, Harris ergodic in the mission's total-variation encoding: $\|P^n(x,\cdot) - \pi\| \to 0$ for every starting point $x$. Then for every $x \in \mathsf{X}$ and every measurable set $A$,
--   $$P^n(x, A) \;\longrightarrow\; \pi(A) \qquad (n \to \infty).$$
--
--   This is the set-wise content of the total-variation convergence (2) of the source: the total variation distance dominates the difference of the two measures on any measurable set, $|P^n(x,A) - \pi(A)| \le \|P^n(x,\cdot) - \pi\|$, so pointwise convergence on every set follows from convergence in total variation. It is infrastructure for translating the mission's `HarrisErgodic` predicate into the classical hypotheses (irreducibility, aperiodicity) of Meyn and Tweedie.
--
--   **Formalization Note** The $n$-step probabilities and $\pi(A)$ are compared after coercion to $\mathbb{R}$ (`ENNReal.toReal`), which is harmless since all measures involved are probability measures.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 2, eq. (2) (arXiv v2 p. 3); the inequality |mu(A) - nu(A)| <= ||mu - nu|| is the definition of the total variation norm in Section 2

import Definitions.Def_MarkovErgodicity

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.tendsto_iterKernel_apply_toReal_of_harrisErgodic {X : Type*}
    [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hP : HarrisErgodic P π) (x : X) (A : Set X)
    (hA : MeasurableSet A) :
    Tendsto (fun n => ((iterKernel P n) x A).toReal) atTop (𝓝 (π A).toReal) := by sorry
