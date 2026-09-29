-- Prove2me | Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
-- name    : MarkovChainCLT.map_coord_chainMeasure
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T15:16:41.82753+00:00
-- url     : https://prove2.me/theorems/77038cb2-4058-4d3e-9285-fa5e368e4367
-- title:
--   Every coordinate of the stationary chain has law $\pi$
-- statement:
--   Let $P$ be a Markov kernel with invariant probability distribution $\pi$, and run the chain from $X_0 \sim \pi$. Then every coordinate has the same marginal law:
--
--   $$X_n \sim \pi \qquad \text{for all } n \ge 0.$$
--
--   Equivalently, the pushforward of the trajectory law under the $n$-th coordinate projection is $\pi$. This is immediate from invariance by induction: the law of $X_{n+1}$ is the law of $X_n$ pushed through $P$, and $\pi P = \pi$.
--
--   It is the fact used to identify $E[f(X_n)]$ with $E_\pi f$ — in particular to check that the centred functional $Y_n = f(X_n) - E_\pi f$ has mean zero, which is a standing hypothesis of the mixing central limit theorems of the mission — and to transfer moment conditions such as $E_\pi f^2 < \infty$ from $\pi$ to the path measure.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 1 (eq. (1)) and Section 4: E_pi f is the mean of f(X_n) under the stationary chain.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.map_coord_chainMeasure {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (n : ℕ) :
    Measure.map (fun ω : ℕ → X => ω n) (chainMeasure P π) = π := by sorry
