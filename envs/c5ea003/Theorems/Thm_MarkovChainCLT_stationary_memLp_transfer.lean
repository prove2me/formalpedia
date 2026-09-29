-- Prove2me | Theorems.Thm_MarkovChainCLT_stationary_memLp_transfer
-- name    : MarkovChainCLT.stationary_memLp_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:44:47.443297+00:00
-- url     : https://prove2.me/theorems/39ec3523-8a7e-4312-8bba-f3b5273fad30
-- title:
--   Stationarity preserves $L^2$
-- statement:
--   Stationarity preserves square-integrability.
--
--   If $Y_0,Y_1,\dots$ is strictly stationary with $Y_0\in L^2$, then every $Y_k\in L^2$, since each has the law of $Y_0$.
--
--   **Formalization Note** Via pushforward laws and `memLp_map_measure_iff`.
-- source:
--   Standard stationarity; cf. proved rho-route template

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.stationary_memLp_transfer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (hL2 : MemLp (Y 0) 2 P) : ∀ k : ℕ, MemLp (Y k) 2 P := by sorry
