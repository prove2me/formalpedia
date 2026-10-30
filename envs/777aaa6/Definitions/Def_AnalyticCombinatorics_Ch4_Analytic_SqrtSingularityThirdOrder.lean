-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularityThirdOrder
-- name    : AnalyticCombinatorics_Ch4_Analytic_SqrtSingularityThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-27T02:31:40.955866+00:00
-- url     : https://prove2.me/theorems/58aa0fe5-8b90-4934-a570-5b49a190d934
-- title:
--   Third-order coefficients from a rescaled square-root singularity
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def sqrtSingularityC2Rescaled (B0 B1 B2 : ℂ) : ℂ :=
--     -(25 : ℂ) * B0 / (((256 * Real.sqrt Real.pi : ℝ) : ℂ)) -
--       (45 : ℂ) * B1 / (((32 * Real.sqrt Real.pi : ℝ) : ℂ)) -
--         (15 : ℂ) * B2 / (((16 * Real.sqrt Real.pi : ℝ) : ℂ))
--   ```
--
--   ```lean
--   def sqrtSingularityC2 (ρ : ℝ) (Bρ Bderivρ Bsecondρ : ℂ) : ℂ :=
--     sqrtSingularityC2Rescaled Bρ (((ρ : ℝ) : ℂ) * Bderivρ)
--       ((((ρ : ℝ) : ℂ) ^ 2) * Bsecondρ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/SqrtSingularityThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

noncomputable section

def sqrtSingularityC2Rescaled (B0 B1 B2 : ℂ) : ℂ :=
  -(25 : ℂ) * B0 / (((256 * Real.sqrt Real.pi : ℝ) : ℂ)) -
    (45 : ℂ) * B1 / (((32 * Real.sqrt Real.pi : ℝ) : ℂ)) -
      (15 : ℂ) * B2 / (((16 * Real.sqrt Real.pi : ℝ) : ℂ))

def sqrtSingularityC2 (ρ : ℝ) (Bρ Bderivρ Bsecondρ : ℂ) : ℂ :=
  sqrtSingularityC2Rescaled Bρ (((ρ : ℝ) : ℂ) * Bderivρ)
    ((((ρ : ℝ) : ℂ) ^ 2) * Bsecondρ)

def sqrtSingularityRelativeC2 (B0 B1 B2 : ℂ) : ℂ :=
  (25 / 128 : ℂ) + (45 / 16 : ℂ) * B1 / B0 +
    (15 / 8 : ℂ) * B2 / B0

def sqrtHalfModel0 : ℝ :=
  1 / Real.sqrt Real.pi

def sqrtHalfModel1 : ℝ :=
  -(1 / (8 * Real.sqrt Real.pi))

def sqrtHalfModel2 : ℝ :=
  1 / (128 * Real.sqrt Real.pi)

def sqrtHalfThirdModel (n : ℕ) : ℝ :=
  sqrtHalfModel0 * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
    sqrtHalfModel1 * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
      sqrtHalfModel2 * (n : ℝ) ^ (-(5 / 2 : ℝ))

def sqrtModel0Third (n : ℕ) : ℝ :=
  -(1 / (2 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(3 / 2 : ℝ)) -
    (3 / (16 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(5 / 2 : ℝ)) -
      (25 / (256 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(7 / 2 : ℝ))

def sqrtModel1Third (n : ℕ) : ℝ :=
  (3 / (4 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
    (45 / (32 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(7 / 2 : ℝ))

def sqrtModel2Third (n : ℕ) : ℝ :=
  -(15 / (8 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(7 / 2 : ℝ))

end


