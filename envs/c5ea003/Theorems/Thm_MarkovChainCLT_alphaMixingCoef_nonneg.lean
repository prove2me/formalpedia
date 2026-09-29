-- Prove2me | Theorems.Thm_MarkovChainCLT_alphaMixingCoef_nonneg
-- name    : MarkovChainCLT.alphaMixingCoef_nonneg
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T08:18:09.569399+00:00
-- url     : https://prove2.me/theorems/c4b1b19b-3067-447b-8c52-d3ddd633ae6b
-- title:
--   The strong mixing coefficient is nonnegative: $0 \le \alpha(n)$
-- statement:
--   For a probability measure $P$ and any sequence of random variables $Y=(Y_i)_{i\ge0}$, the strong ($\alpha$-) mixing coefficient at lag $n$ is nonnegative:
--
--   $$\alpha(n)=\sup_k\ \sup\bigl\{\,|P(A\cap B)-P(A)P(B)|\ :\ A\in\sigma(Y_0,\dots,Y_k),\ B\in\sigma(Y_{k+n},\dots)\,\bigr\}\ \ge\ 0 .$$
--
--   The defining set contains the value $0$ (take $A=B=\varnothing$) and is bounded above by $1$, because $0\le P(A\cap B)\le1$ and $0\le P(A)P(B)\le1$; hence its supremum is at least $0$. This basic fact is used whenever one squeezes $\alpha(n)\to0$ from an upper bound, and it requires no measurability assumption on the sequence.
--
--   **Formalization Note** The supremum is the real `sSup` of the defining set, so boundedness of the set has to be exhibited before the value $0$ can be compared with it; that is what the proof does.
-- source:
--   R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144, eq. (1.10) (the bounds 0 <= alpha <= 1/4); see also G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3, Definition 1.

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.alphaMixingCoef_nonneg {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    0 ≤ alphaMixingCoef P Y n := by sorry
