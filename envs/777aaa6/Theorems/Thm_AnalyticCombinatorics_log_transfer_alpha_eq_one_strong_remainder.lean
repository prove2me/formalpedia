-- Prove2me | Theorems.Thm_AnalyticCombinatorics_log_transfer_alpha_eq_one_strong_remainder
-- name    : AnalyticCombinatorics.log_transfer_alpha_eq_one_strong_remainder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:46:25.630431+00:00
-- url     : https://prove2.me/theorems/98a5ec1a-02a4-49cc-b626-189e845a6fba
-- title:
--   Logarithmic transfer at exponent one with a strong remainder
-- statement:
--   Let $C\in\mathbb C\setminus\{0\}$, $R>1$, $0<\phi<\pi/2$. Let $f$ have the specified formal multilinear power series $p$ at $0$, and be analytic on a neighbourhood of every point of the source dented domain $\Delta(R,\phi)$ (`DeltaDomainArg`). All limits at $1$ below are taken within that domain. Write $L_\alpha(z)=(1-z)^{-\alpha}[-\log(1-z)]$, with the source complex powers and logarithm. If $\lVert f(z)-CL_1(z)\rVert\,|1-z|\to0$, then $$p_n\sim C\log n.$$ The stated remainder is the strong exponent-one condition, with no division by a logarithm.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogAlphaOneTransfer.lean#L50. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogTransfer
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Boundary logarithmic transfer at α = 1

This file records the first α≤1 transfer: the strong-remainder logarithmic transfer at
`α = 1`, whose model coefficient scale is `log n`.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

theorem AnalyticCombinatorics.log_transfer_alpha_eq_one_strong_remainder
    {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSingularityFun (1 : ℂ) z‖ * ‖(1 : ℂ) - z‖)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((Real.log n : ℝ) : ℂ))) := by sorry
