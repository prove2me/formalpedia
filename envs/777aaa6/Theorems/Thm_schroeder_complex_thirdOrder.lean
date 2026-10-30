-- Prove2me | Theorems.Thm_schroeder_complex_thirdOrder
-- name    : schroeder_complex_thirdOrder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:31:40.895996+00:00
-- url     : https://prove2.me/theorems/634d089b-3bd4-4ed7-84e1-c812db7ad7f3
-- title:
--   Complex third-order large-Schröder expansion
-- statement:
--   Let $s_n$ be the source large-Schröder sequence and $\rho=3-2\sqrt2$. Use the source complex constants $L=\texttt{schroederThirdLeadingConstantℂ}$, $a=\texttt{schroederRelativeSecondMetaConstantℂ}$ and $b=\texttt{schroederRelativeThirdMetaConstantℂ}$, whose literal definitions are retained below in the source model blocks. Then $$s_n-\rho^{-n}L n^{-3/2}(1+a n^{-1}+b n^{-2})=o(\|\rho^{-n}n^{-7/2}\|).$$ All terms are embedded in $\mathbb C$ exactly as in the source; no real simplification or extra tree-count interpretation is asserted.
--
--   The source constants are specified exactly by:
--
--   ```lean
--   def schroederThirdLeadingConstantℂ : ℂ :=
--     sqrtSingularityC0 schroederSingularCoeff
--   ```
--
--   ```lean
--   def schroederRelativeSecondMetaConstantℂ : ℂ :=
--     sqrtSingularityC1 schroederRho schroederSingularCoeff schroederSingularDerivAtRho /
--       schroederThirdLeadingConstantℂ
--   ```
--
--   ```lean
--   def schroederRelativeThirdMetaConstantℂ : ℂ :=
--     sqrtSingularityC2 schroederRho schroederSingularCoeff schroederSingularDerivAtRho
--         schroederSingularSecondDerivAtRho /
--       schroederThirdLeadingConstantℂ
--   ```
--
--   ```lean
--   def schroederSingularDerivAtRho : ℂ :=
--     -schroederSecondSingularCoeff / schroederRhoℂ
--   ```
--
--   ```lean
--   def schroederSingularSecondDerivAtRho : ℂ :=
--     2 * schroederThirdSingularCoeff / schroederRhoℂ ^ 2
--   ```
--
--   ```lean
--   def schroederThirdSingularCoeff : ℂ :=
--     -2 * schroederThirdKℂ / schroederOneSubRhoℂ ^ 2
--   ```
--
--   ```lean
--   def schroederThirdKℂ : ℂ :=
--     schroederSqrtRegularAtOneℂ + schroederSqrtRegularLinearCoeff +
--       schroederSqrtRegularQuadraticCoeff
--   ```
--
--   ```lean
--   def schroederSqrtRegularLinearCoeff : ℂ :=
--     schroederRhoℂ ^ 2 / (2 * schroederSqrtRegularAtOneℂ)
--   ```
--
--   ```lean
--   def schroederSqrtRegularQuadraticCoeff : ℂ :=
--     -(schroederRhoℂ ^ 4) / (8 * schroederSqrtRegularAtOneℂ ^ 3)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/SchroederThirdOrder.lean#L699. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularitySecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularityThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Schroeder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_SchroederSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_SchroederThirdOrder
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order large Schroeder asymptotics

This file plugs the large-Schroeder square-root data at
`ρ = 3 - 2 * sqrt 2` into the third-order square-root applicator.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

theorem schroeder_complex_thirdOrder :
    (fun n : ℕ =>
      (schroeder n : ℂ) -
        (schroederRhoℂ⁻¹) ^ n * schroederThirdLeadingConstantℂ *
          (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (1 + schroederRelativeSecondMetaConstantℂ *
              (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) +
            schroederRelativeThirdMetaConstantℂ *
              (((n : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop]
        (fun n : ℕ =>
          ‖((schroederRhoℂ⁻¹) ^ n *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by sorry
