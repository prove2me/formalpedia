-- Prove2me | Theorems.Thm_MarkovChainCLT_cov_abs_le_sqrt_var
-- name    : MarkovChainCLT.cov_abs_le_sqrt_var
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:20:55.035019+00:00
-- url     : https://prove2.me/theorems/524bafe5-1f6d-4d39-8e03-0eaba54ef6b3
-- title:
--   Cauchy-Schwarz for covariance
-- statement:
--   Cauchy-Schwarz inequality for covariance.
--
--   Let $U,V$ be real random variables on a probability space $(\Omega,\mathcal F,P)$ with $E[U^2],E[V^2]<\infty$. Writing $\mu_U=E[U]$, $\mu_V=E[V]$, $\mathrm{Cov}(U,V)=E[(U-\mu_U)(V-\mu_V)]$ and $\mathrm{Var}(U)=E[(U-\mu_U)^2]$, we have
--
--   $$
--   |\mathrm{Cov}(U,V)|\le\sqrt{\mathrm{Var}(U)}\sqrt{\mathrm{Var}(V)}.
--   $$
--
--   This is H\"older with $p=q=2$ applied to $|U-\mu_U|$, $|V-\mu_V|$, using $|\int fg|\le\int|fg|$.
--
--   **Formalization Note** Lean writes covariance as `cov[U,V;P]` and variance as `Var[U;P]`.
-- source:
--   Standard probability theory; Hölder with p=q=2, cf. Mathlib integral_mul_le_Lp_mul_Lq_of_nonneg

import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.cov_abs_le_sqrt_var {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (U V : Ω → ℝ) (hU : MemLp U 2 P) (hV : MemLp V 2 P) : |cov[U, V; P]| ≤ Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) := by sorry
