-- Prove2me | Theorems.Thm_MarkovChainCLT_indicator_cov_le_phi
-- name    : MarkovChainCLT.indicator_cov_le_phi
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:04:37.198801+00:00
-- url     : https://prove2.me/theorems/bc3610d8-6e89-4af9-9279-699997da00d6
-- title:
--   Indicator covariance bounded by $\varphi$-mixing coefficient
-- statement:
--   Let $Y_0,Y_1,\dots$ be random variables on a probability space $(\Omega,\mathcal F,P)$, and let $\varphi(n)$ be the uniform mixing coefficient at lag $n$. Let $k\ge 0$, $A\in\sigma(Y_0,\dots,Y_k)$ with $P(A)\neq 0$, and $B\in\sigma(Y_{k+n},\dots)$. Then
--
--   $$
--   |P(A\cap B)-P(A)P(B)|\le\varphi(n).
--   $$
--
--   In words, the covariance of past and future indicators is controlled by $\varphi(n)$: writing the left side as $P(A)\cdot|P(B\mid A)-P(B)|$ exhibits it as $P(A)$ times an element of the supremum defining $\varphi(n)$, and $P(A)\le 1$. Each element of that supremum lies in $[0,1]$, so the supremum dominates it.
--
--   **Formalization Note** Lean encodes $\varphi(n)$ as a real supremum over $k,A,B$; conditional probability is $(P(A\cap B)).toReal/(P(A)).toReal$.
-- source:
--   Galin L. Jones, On the Markov chain central limit theorem, Probability Surveys 1 (2004) 299-320, Sec 3 Definition 3; Richard C. Bradley, Basic Properties of Strong Mixing Conditions, Sec 1, phi-mixing definition and eq. (1.13) context

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.indicator_cov_le_phi {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ) (A B : Set Ω) (hA : MeasurableSet[processSigma Y (Set.Iic k)] A) (hA0 : P A ≠ 0) (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) : |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ≤ phiMixingCoef P Y n := by sorry
