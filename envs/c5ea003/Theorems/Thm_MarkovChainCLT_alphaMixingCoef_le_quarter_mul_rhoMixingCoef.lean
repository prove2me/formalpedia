-- Prove2me | Theorems.Thm_MarkovChainCLT_alphaMixingCoef_le_quarter_mul_rhoMixingCoef
-- name    : MarkovChainCLT.alphaMixingCoef_le_quarter_mul_rhoMixingCoef
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T07:23:52.651901+00:00
-- url     : https://prove2.me/theorems/13366c35-841f-4763-a817-291fa8b2c00f
-- title:
--   Comparison of mixing coefficients: $\alpha(n)\le\rho(n)/4$
-- statement:
--   For a measurable sequence $Y=(Y_i)_{i\ge 0}$ of random elements on a probability space, the strong mixing coefficient is dominated by a quarter of the maximal-correlation coefficient at the same lag:
--
--   $$\alpha(n)\ \le\ \tfrac14\,\rho(n)\qquad (n\ge 0).$$
--
--   Here $\alpha(n)$ is the supremum of $|P(A\cap B)-P(A)P(B)|$ over events $A$ in the past $\sigma(Y_0,\dots,Y_k)$ and $B$ in the future $\sigma(Y_{k+n},Y_{k+n+1},\dots)$, and $\rho(n)$ is the supremum of $|\mathrm{corr}(U,V)|$ over square-integrable $U,V$ measurable with respect to those same two $\sigma$-algebras.
--
--   The inequality is one of the standard comparisons between the classical mixing coefficients, and is what allows a $\rho$-mixing hypothesis to be fed into results stated for strongly mixing sequences: summability, or mere convergence to zero, of $\rho(n)$ implies the same for $\alpha(n)$.
--
--   The proof tests the supremum defining $\rho(n)$ against the indicator variables $U=\mathbf 1_A$, $V=\mathbf 1_B$. Their covariance is exactly $P(A\cap B)-P(A)P(B)$, and their variances are $P(A)(1-P(A))\le\tfrac14$ and $P(B)(1-P(B))\le\tfrac14$, so the correlation quotient contributes the factor $\tfrac14$. If one of the two variances vanishes, then the corresponding event has probability $0$ or $1$ and the covariance vanishes outright.
--
--   **Formalization Note** The measurability hypothesis on $Y$ is what makes events of the past and future $\sigma$-algebras measurable in the ambient space, which is needed for the indicator variables to be square-integrable test functions.
-- source:
--   R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144, eq. (1.11) (the inequality 4 alpha(n) <= rho(n)); see also I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables (1971), Ch. 17. Used in the setting of G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 3 (Definitions 1-2).

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.alphaMixingCoef_le_quarter_mul_rhoMixingCoef
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    alphaMixingCoef P Y n ≤ rhoMixingCoef P Y n / 4 := by sorry
