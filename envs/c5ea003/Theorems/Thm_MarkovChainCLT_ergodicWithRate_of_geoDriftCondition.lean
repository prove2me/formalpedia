-- Prove2me | Theorems.Thm_MarkovChainCLT_ergodicWithRate_of_geoDriftCondition
-- name    : MarkovChainCLT.ergodicWithRate_of_geoDriftCondition
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-04T20:11:07.326473+00:00
-- url     : https://prove2.me/theorems/5076ee11-b700-40ae-91f3-cfcbd1b6ad8a
-- title:
--   Geometric drift gives a total-variation rate proportional to $V$ (Meyn-Tweedie Thm 15.0.1)
-- statement:
--   Let $X$ be a Harris ergodic Markov chain with transition kernel $P$ and invariant probability distribution $\pi$. Suppose a measurable function $V : \mathsf{X} \to [1,\infty)$ satisfies the geometric drift condition towards a measurable small set $C$: $V$ is integrable under every $P(x,\cdot)$ and, for some $d > 0$ and some $b$,
--   $$\Delta V(x) = PV(x) - V(x) \le -d\,V(x) + b\,\mathbb{1}_C(x) \qquad (x \in \mathsf{X}).$$
--   Then the chain converges geometrically in total variation with a rate constant proportional to $V$: there are $R \ge 0$ and $0 \le \rho < 1$ with
--   $$\|P^n(x,\cdot) - \pi\| \le R\,V(x)\,\rho^n \qquad (x \in \mathsf{X},\ n \ge 1).$$
--
--   This is the direction "drift (5) $\Rightarrow$ geometrically ergodic" of Theorem 15.0.1 of Meyn and Tweedie (1993), restricted from the $V$-norm to the total-variation norm, and it is the content of the source's Remark 1 that under the drift condition "we can take $M(x) \propto V(x)$" in the rate bound (3).
--
--   **Formalization Note** Harris ergodicity is the mission's total-variation encoding (`HarrisErgodic`), which supplies the $\psi$-irreducibility and aperiodicity needed for convergence to $\pi$; the conclusion is the platform's `ErgodicWithRate` with constant $x \mapsto R\,V(x)$ and rate $n \mapsto \rho^n$, exactly the shape consumed by the mission's geometric ergodicity predicate. The $\sigma$-algebra of the state space is assumed countably generated (`MeasurableSpace.CountablyGenerated X`), the standing assumption of Meyn and Tweedie (1993, Section 3.1) on which the existence of small sets (their Theorem 5.2.2) rests; the mission's Theorem 1(i) milestone carries the same hypothesis.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 2, Remark 1 (arXiv v2 pp. 3-4); original: S. P. Meyn & R. L. Tweedie, Markov Chains and Stochastic Stability (1993), Theorem 15.0.1 ((iii) => (i)); standing assumption: Meyn & Tweedie (1993), Section 3.1 (countably generated sigma-field) and Theorem 5.2.2 (existence of small sets)

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovDriftMinorization

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.ergodicWithRate_of_geoDriftCondition {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π)
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (d b : ℝ) (hd : 0 < d) (hdrift : GeoDriftCondition P V d b C) :
    ∃ R ρ : ℝ, 0 ≤ R ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ErgodicWithRate P π (fun x => R * V x) (fun n => ρ ^ n) := by sorry
