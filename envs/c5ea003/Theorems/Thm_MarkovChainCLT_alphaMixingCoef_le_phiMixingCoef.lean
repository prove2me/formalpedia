-- Prove2me | Theorems.Thm_MarkovChainCLT_alphaMixingCoef_le_phiMixingCoef
-- name    : MarkovChainCLT.alphaMixingCoef_le_phiMixingCoef
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-04T22:58:56.635277+00:00
-- url     : https://prove2.me/theorems/0d2efa92-4746-401e-beae-e98508b3460c
-- title:
--   $\\alpha(n) \\le \\varphi(n)$: strong mixing is dominated by uniform mixing
-- statement:
--   For a strictly stationary or arbitrary sequence $(Y_i)_{i\ge0}$ of random variables on a probability space, the strong (α-) mixing coefficient is dominated by the uniform (φ-) mixing coefficient at every lag:
--
--   $$\alpha(n) \;\le\; \varphi(n).$$
--
--   Recall the two definitions. Writing $\mathcal A_k = \sigma(Y_0,\dots,Y_k)$ and $\mathcal B_{k+n} = \sigma(Y_{k+n}, Y_{k+n+1},\dots)$,
--
--   $$\alpha(n) = \sup_{k}\ \sup\bigl\{ |P(A \cap B) - P(A)P(B)| : A \in \mathcal A_k,\ B \in \mathcal B_{k+n} \bigr\},$$
--
--   $$\varphi(n) = \sup_{k}\ \sup\bigl\{ |P(B \mid A) - P(B)| : A \in \mathcal A_k,\ P(A) \neq 0,\ B \in \mathcal B_{k+n} \bigr\}.$$
--
--   The comparison is immediate from the identity $|P(A\cap B) - P(A)P(B)| = P(A)\,|P(B \mid A) - P(B)|$ together with $P(A) \le 1$; the case $P(A) = 0$, which is excluded from the definition of $\varphi$, contributes the value $0$ and is covered by the nonnegativity of $\varphi$ (its defining set contains $0$, taking $A = B = \Omega$). Since both coefficients are defined as suprema, the argument also uses that the set defining $\varphi$ is bounded above by $1$, so that each of its elements is at most $\varphi(n)$.
--
--   This is the elementary end of the standard chain of comparisons between mixing coefficients, $2\alpha \le \beta \le \varphi$, and it lets a uniform-mixing hypothesis be fed into any result stated for strongly mixing sequences.
-- source:
--   R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144, arXiv:math/0511078v1, Section 1.1, eq. (1.11)-(1.12) (the chain 2 alpha(A,B) <= beta(A,B) <= phi(A,B)); the coefficients themselves are Definitions 1 and 3 of G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3.

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory

theorem MarkovChainCLT.alphaMixingCoef_le_phiMixingCoef
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    alphaMixingCoef P Y n ≤ phiMixingCoef P Y n := by sorry
