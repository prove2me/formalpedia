-- Prove2me | Theorems.Thm_MarkovChainCLT_geoDriftCondition_of_geometricallyErgodic
-- name    : MarkovChainCLT.geoDriftCondition_of_geometricallyErgodic
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-04T20:10:56.575516+00:00
-- url     : https://prove2.me/theorems/96e16c16-32d2-4722-874e-e81f74bd3958
-- title:
--   Geometric ergodicity yields a geometric drift condition towards a small set (Meyn-Tweedie Thm 15.0.1)
-- statement:
--   Let $X$ be a Harris ergodic Markov chain with transition kernel $P$ and invariant probability distribution $\pi$, and suppose $X$ is **geometrically ergodic**: there are a function $M \ge 0$ and a constant $t < 1$ with
--   $$\|P^n(x,\cdot) - \pi\| \le M(x)\,t^n \qquad (x \in \mathsf{X},\ n \ge 1).$$
--   Then $X$ satisfies a **geometric drift condition**: there exist a measurable function $V : \mathsf{X} \to [1,\infty)$, a measurable small set $C$ (a set carrying a minorization $P^{n_0}(x,\cdot) \ge \varepsilon\,Q(\cdot)$ for all $x \in C$), and constants $d > 0$, $b$ with $V$ integrable under every $P(x,\cdot)$ and
--   $$\Delta V(x) = PV(x) - V(x) \le -d\,V(x) + b\,\mathbb{1}_C(x) \qquad (x \in \mathsf{X}).$$
--
--   This is the direction "geometrically ergodic $\Rightarrow$ drift (5)" of the classical equivalence between geometric ergodicity and the geometric drift condition (Meyn and Tweedie 1993, Theorem 15.0.1 and Chapter 16), invoked in the source's Remark 1 as "geometric ergodicity is equivalent to (5)". Together with its two companions (the $\pi$-integrability of $V$ and the total-variation rate proportional to $V$) it is what lets a geometrically ergodic chain be routed through the drift machinery with a $\pi$-integrable rate constant.
--
--   **Formalization Note** Harris ergodicity is the mission's total-variation encoding (`HarrisErgodic`: $\pi$ invariant and $\|P^n(x,\cdot) - \pi\| \to 0$ from every $x$), which supplies the $\psi$-irreducibility and aperiodicity assumed by Meyn and Tweedie. The drift function is required to be finite and at least $1$ everywhere, and the drift condition carries the integrability of $V$ under each $P(x,\cdot)$ as a conjunct, following the platform definition `GeoDriftCondition`. The $\sigma$-algebra of the state space is assumed countably generated (`MeasurableSpace.CountablyGenerated X`), the standing assumption of Meyn and Tweedie (1993, Section 3.1) on which the existence of small sets (their Theorem 5.2.2) rests; the mission's Theorem 1(i) milestone carries the same hypothesis.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 2, Remark 1 (arXiv v2 pp. 3-4); original: S. P. Meyn & R. L. Tweedie, Markov Chains and Stochastic Stability (1993), Theorem 15.0.1 ((i) => (iii)) and Chapter 16; standing assumption: Meyn & Tweedie (1993), Section 3.1 (countably generated sigma-field) and Theorem 5.2.2 (existence of small sets)

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovDriftMinorization

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.geoDriftCondition_of_geometricallyErgodic {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π) :
    ∃ V : X → ℝ, Measurable V ∧ (∀ x, 1 ≤ V x) ∧
      ∃ C : Set X, MeasurableSet C ∧ IsSmallSet P C ∧
        ∃ d b : ℝ, 0 < d ∧ GeoDriftCondition P V d b C := by sorry
