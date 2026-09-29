-- Prove2me | Theorems.Thm_Zeta23_LeafIntegrals_Ig_core
-- name    : Zeta23.LeafIntegrals.Ig_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:59.635853+00:00
-- url     : https://prove2.me/theorems/ecdad059-64be-420c-8e4c-c20eeb1ea07a
-- title:
--   Core bound (Ig): $\int_T^{2T} \bigl(1+\min(\tau-T,\,2T-\tau)\bigr)^{-2} d\tau \le 2$
-- statement:
--   For every real $T > 0$, the Lebesgue integral over the window $[T, 2T]$ of the inverse-square weight built from the distance to the nearer endpoint satisfies
--
--   $$\int_{[T,\,2T]} \frac{d\tau}{\bigl(1 + \min(\tau - T,\; 2T - \tau)\bigr)^{2}} \;\le\; 2.$$
--
--   The proof splits the window at its midpoint and compares each half with the exact one-sided integrals `integral_left` and `integral_right`, each of value $1 - 1/(1+T) \le 1$.
--
--   **Role.** A self-contained elementary leaf (imports only Mathlib) used as a drop-in by the prime-side analysis of Section 5: it is consumed by `Zeta23.PrimeSide.calE1_maj_bound`, part of the error-term estimates of lem:ends for the trace computation of the prime-side matrix.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Defs/LeafIntegrals.lean#L75-L111, docstring tag (Ig)

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Real Set

theorem Zeta23.LeafIntegrals.Ig_core (T : ℝ) (hT : 0 < T) :
    ∫ τ in Icc T (2 * T), ((1 + min (τ - T) (2 * T - τ)) ^ 2)⁻¹ ≤ 2 := by sorry
