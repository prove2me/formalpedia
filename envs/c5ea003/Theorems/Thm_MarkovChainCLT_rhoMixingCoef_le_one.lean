-- Prove2me | Theorems.Thm_MarkovChainCLT_rhoMixingCoef_le_one
-- name    : MarkovChainCLT.rhoMixingCoef_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:25:15.128195+00:00
-- url     : https://prove2.me/theorems/1b849d59-bd73-49d2-8501-748762f74173
-- title:
--   $\rho(n)\le 1$
-- statement:
--   The maximal correlation coefficient is at most one.
--
--   Let $Y_0,Y_1,\dots$ be random variables on a probability space $(\Omega,\mathcal F,P)$ and $n\ge 0$. With $\rho(n)$ the supremum over $k$ and square-integrable $U\in\sigma(Y_0,\dots,Y_k)$, $V\in\sigma(Y_{k+n},\dots)$ of $|\mathrm{corr}(U,V)|$, we have
--
--   $$
--   \rho(n)\le 1.
--   $$
--
--   Each correlation quotient is at most $1$ by Cauchy-Schwarz for covariance (the $0/0$ degenerate case is $0$ by convention), so the supremum is.
--
--   **Formalization Note** Lean encodes $\rho(n)$ as a real supremum of $|\mathrm{cov}|/(\sqrt{\mathrm{Var}_U}\sqrt{\mathrm{Var}_V})$.
-- source:
--   Standard maximal-correlation bound; Cauchy-Schwarz step, cf. Bradley survey Sec 1

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_cov_abs_le_sqrt_var

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.rhoMixingCoef_le_one {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) : rhoMixingCoef P Y n ≤ 1 := by sorry
