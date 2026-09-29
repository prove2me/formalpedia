-- Prove2me | Theorems.Thm_Zeta23_LeafIntegrals_integral_left
-- name    : Zeta23.LeafIntegrals.integral_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:59.030888+00:00
-- url     : https://prove2.me/theorems/c31b4571-f438-4860-96f7-aaa3e438e380
-- title:
--   Left endpoint integral: $\int_T^{2T} (1+(\tau-T))^{-2}\,d\tau \le 1$
-- statement:
--   For every real $T > 0$, the interval integral
--
--   $$\int_T^{2T} \frac{d\tau}{(1 + (\tau - T))^2} \;\le\; 1.$$
--
--   (The exact value is $1 - 1/(1+T)$, computed by the fundamental theorem of calculus with antiderivative $-(1+(\tau-T))^{-1}$.) The integrand is the inverse-square weight measured from the left endpoint $T$ of the window $[T, 2T]$.
--
--   **Role.** One of the two one-sided halves feeding the core bound `Zeta23.LeafIntegrals.Ig_core` ($\int_T^{2T}(1+\min(\tau-T, 2T-\tau))^{-2}\,d\tau \le 2$), a self-contained elementary leaf used by the Section 5 prime-side error estimates.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Defs/LeafIntegrals.lean#L23-L47

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Real Set

theorem Zeta23.LeafIntegrals.integral_left (T : ℝ) (hT : 0 < T) :
    ∫ τ in T..(2 * T), ((1 + (τ - T)) ^ 2)⁻¹ ≤ 1 := by sorry
