-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LittleOTransfer
-- name    : AnalyticCombinatorics_Ch4_Analytic_LittleOTransfer
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:40:34.974513+00:00
-- url     : https://prove2.me/theorems/73f10629-5dc3-4672-8751-6338c87b8ab2
-- title:
--   Circle-integral coefficient bound
-- statement:
--   For a complex function f and any natural n, transferCircleBound is (2π)⁻¹((1-1/n)⁻¹)^n times the interval integral from -π to π of the norm of f((1-1/n)exp(iθ)). All real reciprocals and division are totalized, and the interval integral is the totalized interval integral. The definition imposes neither integrability nor n>1; n=0 and n=1 remain defined. This auxiliary function is not an assumed coefficient estimate.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LittleOTransfer.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Little-o transfer for Δ-analytic functions, β > 1

This file contains the coefficient-level `o` transfer companion to the
circle-only `O` transfer in `OTransfer.lean`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal

noncomputable section

def transferCircleBound (f : ℂ → ℂ) (n : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ * ((1 : ℝ) - 1 / n)⁻¹ ^ n *
    ∫ θ in (-Real.pi)..Real.pi,
      ‖f ((((1 : ℝ) - 1 / n : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖

/-! ### Log-weighted kernel estimate for the natural-remainder transfer

The natural-remainder logarithmic transfer needs the contour integral of
`‖1-z‖^{-β}·(1+|log‖1-z‖|)` (the strong-remainder transfer used the un-weighted
`‖1-z‖^{-β}`).  The crude uniform bound `-log(ρ²+θ²) ≤ 2 log(1/ρ)` collapses the
log-weighted model integral onto the banked no-log `modelKernel_integral_bound`,
so no new contour estimate is required beyond a pointwise real inequality. -/

/-! ### Squared-log-weighted kernel + little-o transfer (natural-remainder log²) -/

/-! ### β = 1 circle kernel (boundary case): ∫‖1-r·exp‖^{-1} = O(log n). -/

/-! ### β = 1 bridge: kernel → coefficient little-o (boundary case). -/

/-! ### β = 1 coefficient little-o (boundary). -/

/-! ### Log^k-weighted circle kernel (k ≥ 1), reducing to the banked log¹ kernel. -/

/-! ### Log^k bridge: kernel → coefficient little-o (k ≥ 1). -/


