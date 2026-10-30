-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularitySecondOrder
-- name    : AnalyticCombinatorics_Ch4_Analytic_SqrtSingularitySecondOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-27T02:29:57.062347+00:00
-- url     : https://prove2.me/theorems/ce1376da-9c92-4e4e-9cb8-e55b32223a2a
-- title:
--   Sqrt Singularity Second Order
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def sqrtSingularityC0 (B0 : ℂ) : ℂ :=
--     -B0 / (((2 * Real.sqrt Real.pi : ℝ) : ℂ))
--   ```
--
--   ```lean
--   def sqrtSingularityC1Rescaled (B0 B1 : ℂ) : ℂ :=
--     -(3 : ℂ) * B0 / (((16 * Real.sqrt Real.pi : ℝ) : ℂ)) -
--       (3 : ℂ) * B1 / (((4 * Real.sqrt Real.pi : ℝ) : ℂ))
--   ```
--
--   ```lean
--   def sqrtSingularityC1 (ρ : ℝ) (Bρ Bderivρ : ℂ) : ℂ :=
--     sqrtSingularityC1Rescaled Bρ (((ρ : ℝ) : ℂ) * Bderivρ)
--   ```
--
--   ```lean
--   def sqrtAdjustedFun (f : ℂ → ℂ) (A0 A1 : ℂ) (z : ℂ) : ℂ :=
--     f z - sqrtLinearAtOneFun A0 A1 z
--   ```
--
--   ```lean
--   def sqrtLinearAtOneFun (A0 A1 : ℂ) (z : ℂ) : ℂ :=
--     (A0 - A1) + A1 * z
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/SqrtSingularitySecondOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
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
# Second-order square-root singularity applicator

This file packages the `α = -1/2` case of
`transfer_twoTerm_secondOrder_general`.  The caller supplies the local
two-term square-root singular expansion after subtracting the analytic constant
and linear terms at the dominant point.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

def sqrtSingularityC0 (B0 : ℂ) : ℂ :=
  -B0 / (((2 * Real.sqrt Real.pi : ℝ) : ℂ))

def sqrtSingularityC1Rescaled (B0 B1 : ℂ) : ℂ :=
  -(3 : ℂ) * B0 / (((16 * Real.sqrt Real.pi : ℝ) : ℂ)) -
    (3 : ℂ) * B1 / (((4 * Real.sqrt Real.pi : ℝ) : ℂ))

def sqrtSingularityC1 (ρ : ℝ) (Bρ Bderivρ : ℂ) : ℂ :=
  sqrtSingularityC1Rescaled Bρ (((ρ : ℝ) : ℂ) * Bderivρ)

def sqrtSingularityRelativeC1 (B0 B1 : ℂ) : ℂ :=
  (3 / 8 : ℂ) + (3 / 2 : ℂ) * B1 / B0

def sqrtLinearAtOneSeries (A0 A1 : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (A0 - A1) + PowerSeries.C A1 * PowerSeries.X

def sqrtLinearAtOneFun (A0 A1 : ℂ) (z : ℂ) : ℂ :=
  (A0 - A1) + A1 * z

def sqrtAdjustedSeries (P : PowerSeries ℂ) (A0 A1 : ℂ) : PowerSeries ℂ :=
  P - sqrtLinearAtOneSeries A0 A1

def sqrtAdjustedFun (f : ℂ → ℂ) (A0 A1 : ℂ) (z : ℂ) : ℂ :=
  f z - sqrtLinearAtOneFun A0 A1 z

end


