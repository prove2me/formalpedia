-- Prove2me | Theorems.Thm_sqrt_singularity_thirdOrder_original_of_rescaled_singularity
-- name    : sqrt_singularity_thirdOrder_original_of_rescaled_singularity
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-27T02:33:40.215619+00:00
-- url     : https://prove2.me/theorems/5004c8ed-8cac-4e01-b38b-5f0a4a13cb20
-- title:
--   Third-order coefficients from a rescaled square-root singularity
-- statement:
--   Fix $\rho>0$, $R>1$, $0<\phi<\pi/2$ and complex parameters $A_0,A_1,B,B_1,B_2$ with $B\ne0$. Assume $F(\rho z)$ has the faithful rescaled series `rescale ρ P` at zero and is analytic on a neighbourhood of the source $\Delta(R,\phi)$. Set $G(z)=F(\rho z)-A_0-A_1(z-1)$, exactly `sqrtAdjustedFun`. Require, within that domain at $1$, $$\left\|G(z)-B(1-z)^{1/2}+\rho B_1(1-z)^{3/2}-\frac{\rho^2B_2}{2}(1-z)^{5/2}\right\||1-z|^{-5/2}\to0.$$ With the exact source coefficient constants $C_0=\texttt{sqrtSingularityC0}(B)$, $C_1=\texttt{sqrtSingularityC1}(\rho,B,B_1)$ and $C_2=\texttt{sqrtSingularityC2}(\rho,B,B_1,B_2)$, $$[z^n]P-\rho^{-n}(C_0n^{-3/2}+C_1n^{-5/2}+C_2n^{-7/2})=o(\|\rho^{-n}n^{-7/2}\|).$$ The complex parameters $B_1,B_2$ are constrained by the displayed remainder; they are not silently assumed to be derivatives. Their exact definitions are retained in the mathematical foundations.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/SqrtSingularityThirdOrder.lean#L1575. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularitySecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularityThirdOrder
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order square-root singularity applicator

This file extends `SqrtSingularitySecondOrder` by keeping the third
half-integer contribution.  The constants are obtained from
`modelCoeff_thirdOrder` through the positive half-model and the exact
coefficient recurrences for `(1 - z)^(1/2)`, `(1 - z)^(3/2)`, and
`(1 - z)^(5/2)`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

theorem sqrt_singularity_thirdOrder_original_of_rescaled_singularity
    {ρ R φ : ℝ} {F : ℂ → ℂ} {P : PowerSeries ℂ}
    {A0 A1 Bρ Bderivρ Bsecondρ : ℂ}
    (hρ : 0 < ρ) (hBρ : Bρ ≠ 0)
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt (fun z : ℂ => F (((ρ : ℝ) : ℂ) * z))
      (PowerSeries.toFMLS (PowerSeries.rescale (((ρ : ℝ) : ℂ)) P)) (0 : ℂ))
    (hΔ : AnalyticOnNhd ℂ (fun z : ℂ => F (((ρ : ℝ) : ℂ) * z))
      (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun (fun w : ℂ => F (((ρ : ℝ) : ℂ) * w)) A0 A1 z -
            Bρ * (1 - z) ^ (1 / 2 : ℂ) -
            (-(((ρ : ℝ) : ℂ) * Bderivρ)) * (1 - z) ^ (3 / 2 : ℂ) -
            ((((ρ : ℝ) : ℂ) ^ 2 * Bsecondρ) / 2) * (1 - z) ^ (5 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(5 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n P -
        (((((ρ : ℝ) : ℂ)⁻¹) ^ n) *
          (sqrtSingularityC0 Bρ *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 ρ Bρ Bderivρ *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 ρ Bρ Bderivρ Bsecondρ *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖(((((ρ : ℝ) : ℂ)⁻¹) ^ n) *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by sorry
