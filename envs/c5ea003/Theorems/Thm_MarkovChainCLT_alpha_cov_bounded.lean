-- Prove2me | Theorems.Thm_MarkovChainCLT_alpha_cov_bounded
-- name    : MarkovChainCLT.alpha_cov_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:49:07.240588+00:00
-- url     : https://prove2.me/theorems/22845952-cddc-4766-96bc-e15fd5308fe5
-- title:
--   Bounded covariance via $\alpha$ (layer-cake)
-- statement:
--   Covariance of bounded past/future variables via $\alpha$.
--
--   Let $U\in\sigma(Y_0,\dots,Y_k)$ and $V\in\sigma(Y_{k+n},\dots)$ with $|U|,|V|\le M$ everywhere. Then
--
--   $$
--   |\mathrm{Cov}(U,V)|\le 4M^2\alpha(n).
--   $$
--
--   By layer-cake, each of $U,V$ is an integral over $[-M,M]$ of indicators of past/future sets; bilinearity plus $|\mathrm{Cov}(1_A,1_B)|\le\alpha(n)$ and Fubini give area $(2M)^2$ times $\alpha(n)$. Needs $Y$ measurable so past/future are sub-$\sigma$-algebras.
--
--   **Formalization Note** Everywhere-bounded (not just a.e.) to keep Fubini simple.
-- source:
--   Ibragimov-Linnik layer-cake covariance estimate; Rio 1993 quantile form, bounded case

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.alpha_cov_bounded {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (U V : Ω → ℝ) (hU : Measurable[processSigma Y (Set.Iic k)] U) (hV : Measurable[processSigma Y (Set.Ici (k + n))] V) (M : ℝ) (hM0 : 0 ≤ M) (hUb : ∀ ω, |U ω| ≤ M) (hVb : ∀ ω, |V ω| ≤ M) : |cov[U, V; P]| ≤ 4 * M ^ 2 * alphaMixingCoef P Y n := by sorry
