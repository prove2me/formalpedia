-- Prove2me | Theorems.Thm_MarkovChainCLT_stationary_mean_transfer
-- name    : MarkovChainCLT.stationary_mean_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:43:42.914942+00:00
-- url     : https://prove2.me/theorems/4966a5fe-6600-4eb3-a268-84852eeb9476
-- title:
--   Stationarity preserves the mean
-- statement:
--   A centered strictly stationary sequence stays centered.
--
--   If $Y_0,Y_1,\dots$ is strictly stationary with $E[Y_0]=0$, then $E[Y_k]=0$ for every $k$, since each $Y_k$ has the law of $Y_0$ (shifting by $k$ and evaluating at $0$).
--
--   **Formalization Note** Uses pushforward laws and `integral_map`.
-- source:
--   Standard stationarity; cf. proved rho-route template

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.stationary_mean_transfer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (hcent : ∫ ω, Y 0 ω ∂P = 0) : ∀ k : ℕ, ∫ ω, Y k ω ∂P = 0 := by sorry
