-- Prove2me | Theorems.Thm_MarkovChainCLT_stationary_sq_moment_transfer
-- name    : MarkovChainCLT.stationary_sq_moment_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:46:07.426448+00:00
-- url     : https://prove2.me/theorems/891b9e8a-9bd8-4a56-93e7-d9aec41dab92
-- title:
--   Stationarity preserves second moments
-- statement:
--   Stationarity preserves second moments.
--
--   If $Y_0,Y_1,\dots$ is strictly stationary, then $E[Y_k^2]=E[Y_0^2]$ for every $k$, since each $Y_k$ has the law of $Y_0$.
--
--   **Formalization Note** Via pushforward laws and `integral_map` with $x\mapsto x^2$.
-- source:
--   Standard stationarity; cf. proved rho-route template

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.stationary_sq_moment_transfer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) : ∀ k : ℕ, ∫ ω, (Y k ω) ^ 2 ∂P = ∫ ω, (Y 0 ω) ^ 2 ∂P := by sorry
