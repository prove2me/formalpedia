-- Prove2me | Theorems.Thm_Zeta23_LeafIntegrals_integral_right
-- name    : Zeta23.LeafIntegrals.integral_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:59.333221+00:00
-- url     : https://prove2.me/theorems/489305d4-9c69-4a83-91cc-088046314283
-- title:
--   Right endpoint integral: $\int_T^{2T} (1+(2T-\tau))^{-2}\,d\tau \le 1$
-- statement:
--   For every real $T > 0$, the interval integral
--
--   $$\int_T^{2T} \frac{d\tau}{(1 + (2T - \tau))^2} \;\le\; 1.$$
--
--   (The exact value is $1 - 1/(1+T)$, by symmetry with the left-endpoint integral.) The integrand is the inverse-square weight measured from the right endpoint $2T$ of the window $[T, 2T]$.
--
--   **Role.** One of the two one-sided halves feeding the core bound `Zeta23.LeafIntegrals.Ig_core` ($\int_T^{2T}(1+\min(\tau-T, 2T-\tau))^{-2}\,d\tau \le 2$), a self-contained elementary leaf used by the Section 5 prime-side error estimates.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Defs/LeafIntegrals.lean#L49-L73

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Real Set

theorem Zeta23.LeafIntegrals.integral_right (T : ℝ) (hT : 0 < T) :
    ∫ τ in T..(2 * T), ((1 + (2 * T - τ)) ^ 2)⁻¹ ≤ 1 := by sorry
