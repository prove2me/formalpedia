-- Prove2me | Theorems.Thm_MarkovChainCLT_exists_iterKernel_pos_of_harrisErgodic
-- name    : MarkovChainCLT.exists_iterKernel_pos_of_harrisErgodic
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-04T20:10:51.432493+00:00
-- url     : https://prove2.me/theorems/27cd640e-c55a-4daa-89ed-40bf6580902e
-- title:
--   Harris ergodicity gives $\pi$-irreducibility from every point
-- statement:
--   Let $P$ be a Markov kernel on a state space $\mathsf{X}$ with invariant probability distribution $\pi$, Harris ergodic in the mission's total-variation encoding: $\|P^n(x,\cdot) - \pi\| \to 0$ for every starting point $x$. Then the chain is $\pi$-irreducible from every point: for every measurable set $A$ with $\pi(A) > 0$ and every $x \in \mathsf{X}$ there is an $n$ with
--   $$P^n(x, A) > 0.$$
--
--   This is $\psi$-irreducibility with $\psi = \pi$ (Meyn and Tweedie 1993, Section 4.2), one of the standing hypotheses under which the drift and minorization theory of the source is stated. It follows from the pointwise convergence $P^n(x,A) \to \pi(A) > 0$ given by the total-variation convergence from every starting point.
--
--   **Formalization Note** The conclusion is stated for every $x$, not just $\pi$-almost every $x$, because the mission's `HarrisErgodic` quantifies the total-variation convergence over every starting point; this is what makes the classical hypothesis available everywhere.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 2, eq. (2) (arXiv v2 p. 3); Meyn & Tweedie (1993), Section 4.2 (psi-irreducibility)

import Definitions.Def_MarkovErgodicity

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.exists_iterKernel_pos_of_harrisErgodic {X : Type*}
    [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hP : HarrisErgodic P π) (A : Set X) (hA : MeasurableSet A)
    (hπA : 0 < π A) (x : X) :
    ∃ n : ℕ, 0 < (iterKernel P n) x A := by sorry
