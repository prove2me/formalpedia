-- Prove2me | Theorems.Thm_MarkovChainCLT_alphaMixingCoef_le_quarter
-- name    : MarkovChainCLT.alphaMixingCoef_le_quarter
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T08:18:21.441337+00:00
-- url     : https://prove2.me/theorems/51bf584c-8d96-4934-9bbd-2bb8c1c316c4
-- title:
--   The strong mixing coefficient satisfies $\alpha(n) \le 1/4$
-- statement:
--   Let $P$ be a probability measure and let $Y=(Y_i)_{i\ge0}$ be a measurable sequence of random variables. Then the strong ($\alpha$-) mixing coefficient at every lag $n$ obeys the universal bound
--
--   $$\alpha(n)\ \le\ \tfrac14 .$$
--
--   Indeed, writing $a=P(A)$, $b=P(B)$ and $c=P(A\cap B)$ for events $A$ and $B$, one has $0\le c\le\min(a,b)$ and $c\ge a+b-1$. Consequently
--
--   $$c-ab\ \le\ \min(a,b)\bigl(1-\max(a,b)\bigr)\ \le\ \tfrac14,\qquad ab-c\ \le\ \max\bigl(ab,\,(1-a)(1-b)\bigr)\ \le\ \tfrac14,$$
--
--   so every element of the set defining $\alpha(n)$ is at most $1/4$, and so is its supremum. Together with nonnegativity this pins $\alpha(n)$ to the interval $[0,1/4]$, the normalisation under which the comparison $\alpha(n)\le\rho(n)/4$ is sharp.
--
--   **Formalization Note** Measurability of the $Y_i$ is assumed so that the events appearing in the definition, which are measurable for the generated past and future $\sigma$-algebras, are measurable for the ambient $\sigma$-algebra; this is what makes the inclusion-exclusion bound $P(A)+P(B)-P(A\cap B)\le1$ available.
-- source:
--   R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144, eq. (1.10); see also G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3, Definition 1.

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.alphaMixingCoef_le_quarter {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    alphaMixingCoef P Y n ≤ 1 / 4 := by sorry
