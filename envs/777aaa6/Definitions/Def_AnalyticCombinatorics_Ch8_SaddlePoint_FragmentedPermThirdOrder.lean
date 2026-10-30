-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:40:46.519491+00:00
-- url     : https://prove2.me/theorems/e08fd998-f3ef-4be5-b3ed-2900e7c8e36e
-- title:
--   Fragmented Perm Third Order
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   def fragPermThirdCorrScale (r : ℝ) : ℝ :=
--     (1 - r) ^ 2
--   ```
--
--   ```lean
--   def fragPermThirdOrderSaddleScale (n : ℕ) : ℂ :=
--     saddleScale fragPermFun fragPermSaddleRadius
--       (fun n => fragPermSaddleBReal (fragPermSaddleRadius n)) n
--   ```
--
--   ```lean
--   def fragPermThirdCorrectionAtSaddle (n : ℕ) : ℝ :=
--     saddleThirdCorrection fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
--       fragPermSaddleB5Real fragPermSaddleB6Real (fragPermSaddleRadius n)
--   ```
--
--   ```lean
--   def fragPermThirdRobustCorrScale (r : ℝ) : ℝ :=
--     fragPermSecondCorrScale r
--   ```
--
--   ```lean
--   def fragPermSaddleB5Real (r : ℝ) : ℝ :=
--     r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) / (1 - r) ^ 6
--   ```
--
--   ```lean
--   def fragPermSaddleB6Real (r : ℝ) : ℝ :=
--     r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) /
--       (1 - r) ^ 7
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Third-order saddle data for fragmented permutations

This file adds the finite-radius third-order correction layer for
`exp (z / (1 - z))`.  The proof uses the narrower finite-radius window
`(1-r)^(29/20)`, because the second-order window is too wide for an
`o((1-r)^2)` third-order remainder.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

noncomputable section

namespace FragmentedPermHAdmissible

/-- Fifth logarithmic saddle derivative for fragmented permutations. -/
def fragPermSaddleB5Real (r : ℝ) : ℝ :=
  r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) / (1 - r) ^ 6

/-- Sixth logarithmic saddle derivative for fragmented permutations. -/
def fragPermSaddleB6Real (r : ℝ) : ℝ :=
  r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) /
    (1 - r) ^ 7

/-- Narrow finite-radius window for the third-order fragmented-permutation proof. -/
def fragPermThirdSaddleDeltaReal (r : ℝ) : ℝ :=
  (1 - r) ^ (29 / 20 : ℝ)

/-- Complex saddle scale used by the fragmented-permutation third-order statement. -/
def fragPermThirdOrderSaddleScale (n : ℕ) : ℂ :=
  saddleScale fragPermFun fragPermSaddleRadius
    (fun n => fragPermSaddleBReal (fragPermSaddleRadius n)) n

/-- The explicit third-order correction at the saddle radius. -/
def fragPermThirdCorrectionAtSaddle (n : ℕ) : ℝ :=
  saddleThirdCorrection fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
    fragPermSaddleB5Real fragPermSaddleB6Real (fragPermSaddleRadius n)

/--
Robust third-order scale accepted by the generic `ThirdOrderHAdmissible`
interface.  The true finite-radius third-order correction is on the smaller
scale `(1-r)^2`; this robust scale is used only to reuse the abstract wrapper.
-/
def fragPermThirdRobustCorrScale (r : ℝ) : ℝ :=
  fragPermSecondCorrScale r

def fragPermThirdScaledCubic (r x : ℝ) : ℂ :=
  -Complex.I *
    ((fragPermSaddleB3Real r : ℂ) /
      (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)) * (x : ℂ) ^ 3

def fragPermThirdScaledQuartic (r x : ℝ) : ℂ :=
  ((fragPermSaddleB4Real r : ℂ) / (24 * (fragPermSaddleBReal r : ℂ) ^ 2)) *
    (x : ℂ) ^ 4

def fragPermThirdScaledFifth (r x : ℝ) : ℂ :=
  Complex.I *
    ((fragPermSaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5

def fragPermThirdScaledSixth (r x : ℝ) : ℂ :=
  -((fragPermSaddleB6Real r : ℂ) / (720 * (fragPermSaddleBReal r : ℂ) ^ 3)) *
    (x : ℂ) ^ 6

def fragPermThirdScaledRemainder (r x : ℝ) : ℂ :=
  fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) -
    fragPermThirdScaledCubic r x - fragPermThirdScaledQuartic r x -
      fragPermThirdScaledFifth r x - fragPermThirdScaledSixth r x

def fragPermThirdScaledRemainderConst : ℝ :=
  200000000000 * Real.exp 6

def fragPermThirdLocalL1Const : ℝ :=
  100000 * (Real.exp 1 + 1) *
    ((100 + fragPermThirdScaledRemainderConst) ^ 5 +
      (100 + fragPermThirdScaledRemainderConst) ^ 4 +
      (100 + fragPermThirdScaledRemainderConst) ^ 3 +
      (100 + fragPermThirdScaledRemainderConst) ^ 2 +
      (100 + fragPermThirdScaledRemainderConst) + 1)

end FragmentedPermHAdmissible


