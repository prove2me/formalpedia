-- Prove2me | Theorems.Thm_MarkovChainCLT_rhoMixingCoef_le_two_mul_sqrt_phiMixingCoef
-- name    : MarkovChainCLT.rhoMixingCoef_le_two_mul_sqrt_phiMixingCoef
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-04T21:08:58.582201+00:00
-- url     : https://prove2.me/theorems/8ceb4c34-56b9-42f7-814d-87e2fc227a43
-- title:
--   $\rho(n)\le 2\sqrt{\varphi(n)}$ (Cogburn--Ibragimov inequality)
-- statement:
--   Let $Y=(Y_n)_{n\ge 0}$ be a sequence of random variables on a probability space $(\Omega,\mathcal F,P)$, and for a lag $n$ let
--
--   $$\varphi(n)=\sup_k\ \sup\bigl\{\,|P(B\mid A)-P(B)|\ :\ A\in\sigma(Y_0,\dots,Y_k),\ P(A)\neq 0,\ B\in\sigma(Y_j: j\ge k+n)\,\bigr\}$$
--
--   be the uniform ($\varphi$-) mixing coefficient and let $\rho(n)$ be the maximal-correlation ($\rho$-) mixing coefficient, the supremum of $|\operatorname{corr}(U,V)|$ over square-integrable $U$ measurable for the past $\sigma(Y_0,\dots,Y_k)$ and $V$ measurable for the future $\sigma(Y_j : j\ge k+n)$.
--
--   Then the two coefficients are comparable through
--
--   $$\rho(n)\ \le\ 2\,\sqrt{\varphi(n)}\qquad (n\ge 0).$$
--
--   Equivalently, at the level of two $\sigma$-fields $\mathcal A,\mathcal B$, this is the classical inequality $\rho(\mathcal A,\mathcal B)\le 2[\varphi(\mathcal A,\mathcal B)]^{1/2}$ of Cogburn and Ibragimov: for $U\in L^2(\mathcal A)$ and $V\in L^2(\mathcal B)$,
--
--   $$|\operatorname{Cov}(U,V)|\ \le\ 2\sqrt{\varphi(\mathcal A,\mathcal B)}\ \sqrt{\operatorname{Var}(U)}\,\sqrt{\operatorname{Var}(V)} .$$
--
--   Taking the supremum over lags $k$ on both sides and using monotonicity of the square root gives the stated form for sequences.
--
--   This is the bridge from uniform mixing to maximal-correlation mixing: it turns the summability hypothesis $\sum_n\sqrt{\varphi(n)}<\infty$ of the Billingsley uniform-mixing central limit theorem into the summability hypothesis $\sum_n\rho(n)<\infty$ of the Ibragimov $\rho$-mixing central limit theorem.
-- source:
--   R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144, arXiv:math/0511078v1, Section 1.1, eq. (1.13): rho(A,B) <= 2[phi(A,B)]^{1/2}[phi(B,A)]^{1/2} <= 2[phi(A,B)]^{1/2}, attributed there to Cogburn (1960) and Ibragimov (1962); see also J. L. Doob, Stochastic Processes (1953), p. 222, Lemma 7.1.

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory

/-- The Cogburn-Ibragimov comparison of the maximal-correlation and uniform mixing
coefficients of a sequence. -/

theorem MarkovChainCLT.rhoMixingCoef_le_two_mul_sqrt_phiMixingCoef
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    rhoMixingCoef P Y n ≤ 2 * Real.sqrt (phiMixingCoef P Y n) := by sorry
