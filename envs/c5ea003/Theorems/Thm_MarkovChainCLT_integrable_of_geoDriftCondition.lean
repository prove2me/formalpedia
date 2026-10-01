-- Prove2me | Theorems.Thm_MarkovChainCLT_integrable_of_geoDriftCondition
-- name    : MarkovChainCLT.integrable_of_geoDriftCondition
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-04T20:11:02.244286+00:00
-- url     : https://prove2.me/theorems/205b10ed-2098-472e-aa21-c5c6d0194b42
-- title:
--   A geometric drift function is $\pi$-integrable (Meyn-Tweedie Thm 14.3.7)
-- statement:
--   Let $X$ be a Harris ergodic Markov chain with transition kernel $P$ and invariant probability distribution $\pi$. Suppose a measurable function $V : \mathsf{X} \to [1,\infty)$ satisfies the geometric drift condition towards a measurable small set $C$: $V$ is integrable under every $P(x,\cdot)$ and, for some $d > 0$ and some $b$,
--   $$\Delta V(x) = PV(x) - V(x) \le -d\,V(x) + b\,\mathbb{1}_C(x) \qquad (x \in \mathsf{X}).$$
--   Then $V$ is $\pi$-integrable:
--   $$E_\pi V = \int V \, d\pi < \infty.$$
--
--   This is Theorem 14.3.7 of Meyn and Tweedie (1993), quoted in the source's Remark 1 as "if (5) holds then $E_\pi V < \infty$". It is the step that turns the drift function of a geometrically ergodic chain into a $\pi$-integrable rate constant, which is the standing side condition $E_\pi M < \infty$ under which the source's Theorem 2(ii) bounds the strong mixing coefficients by the total-variation rate.
--
--   **Formalization Note** Harris ergodicity is the mission's total-variation encoding (`HarrisErgodic`), which gives the invariance of $\pi$ and the $\psi$-irreducibility that Meyn and Tweedie assume; the drift condition is the platform's `GeoDriftCondition`, whose integrability conjunct rules out the vacuous reading of a non-integrable $V$. The $\sigma$-algebra of the state space is assumed countably generated (`MeasurableSpace.CountablyGenerated X`), the standing assumption of Meyn and Tweedie (1993, Section 3.1) on which the existence of small sets (their Theorem 5.2.2) rests; the mission's Theorem 1(i) milestone carries the same hypothesis.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 2, Remark 1 (arXiv v2 pp. 3-4); original: S. P. Meyn & R. L. Tweedie, Markov Chains and Stochastic Stability (1993), Theorem 14.3.7; standing assumption: Meyn & Tweedie (1993), Section 3.1 (countably generated sigma-field) and Theorem 5.2.2 (existence of small sets)

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovDriftMinorization

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.integrable_of_geoDriftCondition {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π)
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (d b : ℝ) (hd : 0 < d) (hdrift : GeoDriftCondition P V d b C) :
    Integrable V π := by sorry
