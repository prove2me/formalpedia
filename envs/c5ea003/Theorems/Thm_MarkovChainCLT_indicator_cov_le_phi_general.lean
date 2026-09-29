-- Prove2me | Theorems.Thm_MarkovChainCLT_indicator_cov_le_phi_general
-- name    : MarkovChainCLT.indicator_cov_le_phi_general
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:15:31.752963+00:00
-- url     : https://prove2.me/theorems/39a15c3d-82c1-4448-9fb2-7a468e31d8d5
-- title:
--   Indicator covariance by $\varphi$, no non-null hypothesis
-- statement:
--   Let $Y_0,Y_1,\dots$ be random variables on a probability space $(\Omega,\mathcal F,P)$ with uniform mixing coefficients $\varphi(n)$. Let $k\ge 0$, $A\in\sigma(Y_0,\dots,Y_k)$ and $B\in\sigma(Y_{k+n},\dots)$, with no non-null assumption. Then
--
--   $$
--   |P(A\cap B)-P(A)P(B)|\le\varphi(n).
--   $$
--
--   If $P(A)=0$ both sides collapse ($P(A\cap B)=0$ and $0\le\varphi(n)$ since $0$ is attained at $A=B=\Omega$); otherwise this is the $P(A)\neq 0$ bound. Removing the side condition makes the lemma directly reusable in covariance estimates.
--
--   **Formalization Note** $\varphi(n)$ is the real supremum over $k,A,B$; conditional probability is $(P(A\cap B)).toReal/(P(A)).toReal$.
-- source:
--   Galin L. Jones, On the Markov chain central limit theorem, Probability Surveys 1 (2004) 299-320, Sec 3 Definition 3; Richard C. Bradley, Basic Properties of Strong Mixing Conditions, Sec 1

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_indicator_cov_le_phi

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.indicator_cov_le_phi_general {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ) (A B : Set Ω) (hA : MeasurableSet[processSigma Y (Set.Iic k)] A) (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) : |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ≤ phiMixingCoef P Y n := by sorry
