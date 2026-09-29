-- Prove2me | Theorems.Thm_MarkovChainCLT_alphaMixingCoef_exp_of_geometricallyErgodic_of_countablyGenerated
-- name    : MarkovChainCLT.alphaMixingCoef_exp_of_geometricallyErgodic_of_countablyGenerated
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T01:26:08.514359+00:00
-- url     : https://prove2.me/theorems/bd5c74b7-77bd-4234-81ce-ead16bfbb08f
-- title:
--   Geometrically ergodic chains are exponentially strongly mixing (countably generated state space)
-- statement:
--   Let $X = \{X_n\}_{n \ge 0}$ be a Markov chain with transition kernel $P$ on a state space $\mathsf{X}$ whose $\sigma$-algebra is **countably generated**, Harris ergodic with invariant probability distribution $\pi$, and suppose the chain is **geometrically ergodic**: there are a function $M \ge 0$ and a constant $t < 1$ with
--
--   $$\|P^n(x, \cdot) - \pi\| \le M(x)\, t^n \qquad (x \in \mathsf{X},\ n \ge 1).$$
--
--   Then the stationary chain (started from $X_0 \sim \pi$) is exponentially fast strongly mixing: there exist $c \ge 0$ and $a \in [0, 1)$ with
--
--   $$\alpha(n) \;\le\; c\, a^n \qquad (n \ge 0).$$
--
--   This is the countably generated case of the source's remark that "geometrically ergodic Markov chains enjoy exponentially fast strong mixing" (Jones 2004, §3), proved exactly along the route the source indicates. By Remark 1 and Meyn–Tweedie Theorem 15.0.1, geometric ergodicity is equivalent to a geometric drift condition $\Delta V \le -d V + b\,\mathbb{1}_C$ towards a small set $C$ for some $V \ge 1$; the drift condition gives back a total-variation rate $\|P^n(x,\cdot) - \pi\| \le R\, V(x)\, \rho^n$ with constant proportional to $V$, and Meyn–Tweedie Theorem 14.3.7 gives $E_\pi V < \infty$. Theorem 2(ii) of the source then bounds the strong mixing coefficients of the stationary chain by the integrated rate, $\alpha(n) \le \rho^n\, R\, E_\pi V$ for $n \ge 1$, and $\alpha(0) \le 1/4$ handles the remaining lag.
--
--   Countable generation of the $\sigma$-algebra is the standing assumption of Meyn and Tweedie (1993, §3.1) under which small sets exist and the splitting construction behind Theorem 15.0.1 is available; the platform's drift-side statements `geoDriftCondition_of_geometricallyErgodic`, `ergodicWithRate_of_geoDriftCondition` and `integrable_of_geoDriftCondition` carry the same hypothesis. The companion statement without this hypothesis, `alphaMixingCoef_exp_of_geometricallyErgodic`, is what Corollaries 2 and 3 cite; it reduces to the present one by passing to a countably generated $P$-invariant sub-$\sigma$-algebra that carries countably many witnesses for all the mixing coefficients at once.
--
--   **Formalization Note** "Harris ergodic" is the mission's total-variation encoding (`HarrisErgodic`: $\pi$ invariant and $\|P^n(x,\cdot) - \pi\| \to 0$ for every $x$) and geometric ergodicity is `GeometricallyErgodic` from `Def_MarkovErgodicity`. The mixing coefficient is `alphaMixingCoef` of the coordinate process $\omega \mapsto \omega_i$ under the stationary path law `chainMeasure P π`, the object bounded by `alpha_mixing_le_tv_rate`. The countably generated hypothesis is the Mathlib instance `MeasurableSpace.CountablyGenerated X`.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 3 (arXiv v2 p. 7): "geometrically ergodic Markov chains enjoy exponentially fast strong mixing", via Section 2, Remark 1 (arXiv v2 pp. 3-4) and Theorem 2(ii) (arXiv v2 p. 8). Original: S. P. Meyn & R. L. Tweedie, Markov Chains and Stochastic Stability (1993), Theorem 15.0.1 (geometric ergodicity iff geometric drift) and Theorem 14.3.7 (E_π V < ∞); standing assumption Section 3.1 (countably generated sigma-field) and Theorem 5.2.2 (existence of small sets).

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.alphaMixingCoef_exp_of_geometricallyErgodic_of_countablyGenerated
    {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π) :
    ∃ c a : ℝ, 0 ≤ c ∧ 0 ≤ a ∧ a < 1 ∧
      ∀ n : ℕ, alphaMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n ≤ c * a ^ n := by sorry
