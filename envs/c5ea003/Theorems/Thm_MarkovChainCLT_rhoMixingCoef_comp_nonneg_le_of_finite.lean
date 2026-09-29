-- Prove2me | Theorems.Thm_MarkovChainCLT_rhoMixingCoef_comp_nonneg_le_of_finite
-- name    : MarkovChainCLT.rhoMixingCoef_comp_nonneg_le_of_finite
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T15:40:11.406813+00:00
-- url     : https://prove2.me/theorems/3ee2c27b-e38f-44ac-ab0a-53e9d3f5fa7d
-- title:
--   Functional processes inherit $\rho$-mixing (finite measure): $0 \le \rho_g(n) \le \rho(n)$
-- statement:
--   Let $P$ be a **finite** measure on $\Omega$, let $Y = \{Y_i\}_{i \ge 0}$ be a sequence of random elements of $\mathsf{X}$, and let $g : \mathsf{X} \to \mathsf{E}$ be measurable. Write $\rho(n)$ for the asymptotically-uncorrelated ($\rho$-) mixing coefficient of $Y$ at lag $n$ and $\rho_g(n)$ for that of the **functional process** $\{g(Y_i)\}_{i \ge 0}$. Then
--
--   $$0 \le \rho_g(n) \le \rho(n) \qquad \text{for every } n \ge 0.$$
--
--   Since $g$ is measurable, $\sigma(g(Y_i) : i \in S) \subseteq \sigma(Y_i : i \in S)$, so the family of event (or variable) pairs over which $\rho_g(n)$ is a supremum is a subfamily of the one defining $\rho(n)$; the inequality is monotonicity of the supremum, and nonnegativity holds because every member of the family is an absolute value.
--
--   **Why finiteness is needed.** The coefficients are defined as suprema of sets of reals, and in Lean the supremum of a set that is not bounded above is $0$ by convention. For a general (non-finite) measure the family defining $\rho(n)$ can be unbounded — making $\rho(n) = 0$ — while the smaller family defining $\rho_g(n)$ stays bounded with a strictly positive supremum, and the inequality then fails. Finiteness of $P$ makes both families bounded above (by $P(\Omega) + P(\Omega)^2$, respectively $1 + P(\Omega)$), which is exactly what makes the comparison of suprema legitimate. In the Markov chain application $P$ is the law of the chain, a probability measure, so the hypothesis is free.
--
--   This is the step "by an earlier remark $\rho_f(n) \le \rho(n)$ for all $n \ge 1$" in Jones's proof of Corollary 1, which lets a mixing central limit theorem stated for a general stationary sequence be applied to the functional process $\{f(X_n)\}$ of a Markov chain.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 4, proof of Corollary 1 (arXiv v2 p. 10): "Let alpha(n) and alpha_f(n) denote the strong mixing coefficients for the Markov chain X = {X_n} and the functional process {f(X_n)}, respectively. By an earlier remark alpha_f(n) <= alpha(n) for all n >= 1."

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.rhoMixingCoef_comp_nonneg_le_of_finite {Ω X E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace E] (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ℕ → Ω → X) (g : X → E) (hg : Measurable g) (n : ℕ) :
    0 ≤ rhoMixingCoef P (fun i ω => g (Y i ω)) n ∧
      rhoMixingCoef P (fun i ω => g (Y i ω)) n ≤ rhoMixingCoef P Y n := by sorry
