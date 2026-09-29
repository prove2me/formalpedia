-- Prove2me | Theorems.Thm_MarkovChainCLT_alpha_indicator_cov_le
-- name    : MarkovChainCLT.alpha_indicator_cov_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:36:10.755212+00:00
-- url     : https://prove2.me/theorems/3bc3f28a-a669-4304-8f86-97a16c471a1f
-- title:
--   Indicator covariance bounded by $\alpha$
-- statement:
--   Indicator covariance controlled by strong mixing.
--
--   Let $Y_0,Y_1,\dots$ be random variables on a probability space with strong mixing coefficients $\alpha(n)$. For $A\in\sigma(Y_0,\dots,Y_k)$ and $B\in\sigma(Y_{k+n},\dots)$,
--
--   $$
--   |P(A\cap B)-P(A)P(B)|\le\alpha(n).
--   $$
--
--   The pair $(A,B)$ is an element of the supremum defining $\alpha(n)$, which is bounded above by $1$.
--
--   **Formalization Note** $\alpha(n)$ is the real supremum over $k,A,B$.
-- source:
--   Jones 2004 Sec 3 Definition 1; Bradley survey Sec 1

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.alpha_indicator_cov_le {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ) (A B : Set Ω) (hA : MeasurableSet[processSigma Y (Set.Iic k)] A) (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) : |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ≤ alphaMixingCoef P Y n := by sorry
