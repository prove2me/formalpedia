-- Prove2me | Theorems.Thm_MarkovChainCLT_processSigma_comp_le
-- name    : MarkovChainCLT.processSigma_comp_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T15:40:04.390292+00:00
-- url     : https://prove2.me/theorems/445c0601-a837-4dea-b2b0-74cee42ba22c
-- title:
--   A measurable functional generates a smaller $\sigma$-algebra
-- statement:
--   Let $Y = \{Y_i\}_{i \ge 0}$ be a family of maps into a measurable space $\mathsf{X}$ and let $g : \mathsf{X} \to \mathsf{E}$ be measurable. Then for every index set $S \subseteq \mathbb{N}$,
--
--   $$\sigma\bigl(g(Y_i) : i \in S\bigr) \;\subseteq\; \sigma\bigl(Y_i : i \in S\bigr).$$
--
--   Indeed $\sigma(g \circ Y_i)$ is the comap of the target $\sigma$-algebra along $g \circ Y_i$, which factors as the comap along $Y_i$ of the comap along $g$; measurability of $g$ says the latter is contained in the $\sigma$-algebra of $\mathsf{X}$, and comap is monotone.
--
--   This is the elementary fact underlying the statement that the mixing coefficients of a *functional* process are dominated by those of the underlying process — the supremum defining the functional coefficient ranges over a subfamily of the pairs of events used for the original one.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 4, proof of Corollary 1 (arXiv v2 p. 10): "Let alpha(n) and alpha_f(n) denote the strong mixing coefficients for the Markov chain X = {X_n} and the functional process {f(X_n)}, respectively. By an earlier remark alpha_f(n) <= alpha(n) for all n >= 1."

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.processSigma_comp_le {Ω X E : Type*} [MeasurableSpace X]
    [MeasurableSpace E] (Y : ℕ → Ω → X) (g : X → E) (hg : Measurable g) (s : Set ℕ) :
    processSigma (fun i ω => g (Y i ω)) s ≤ processSigma Y s := by sorry
