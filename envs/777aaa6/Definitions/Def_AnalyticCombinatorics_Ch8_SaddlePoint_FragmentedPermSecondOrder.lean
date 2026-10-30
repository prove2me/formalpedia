-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:38:18.639044+00:00
-- url     : https://prove2.me/theorems/f6e51554-5b80-44f0-80d9-f4c992850589
-- title:
--   Fragmented Perm Second Order
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   def fragPermSecondCorrScale (r : ℝ) : ℝ :=
--     1 - r
--   ```
--
--   ```lean
--   def fragPermSecondCorrectionAtSaddle (n : ℕ) : ℝ :=
--     saddleCorrection fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
--       (fragPermSaddleRadius n)
--   ```
--
--   ```lean
--   def fragPermSaddleB3Real (r : ℝ) : ℝ :=
--     r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4
--   ```
--
--   ```lean
--   def fragPermSaddleB4Real (r : ℝ) : ℝ :=
--     r * (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (1 - r) ^ 5
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermSecondOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
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
# Second-order saddle data for fragmented permutations

This file adds the second-order correction layer for
`exp (z / (1 - z))`.  The logarithmic saddle derivatives are
`b₃(r) = r(1 + 4r + r²)/(1-r)^4` and
`b₄(r) = r(1 + 11r + 11r² + r³)/(1-r)^5`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

noncomputable section

namespace FragmentedPermHAdmissible

/-- Third logarithmic saddle derivative for fragmented permutations. -/
def fragPermSaddleB3Real (r : ℝ) : ℝ :=
  r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4

/-- Fourth logarithmic saddle derivative for fragmented permutations. -/
def fragPermSaddleB4Real (r : ℝ) : ℝ :=
  r * (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (1 - r) ^ 5

/-- Second-order correction scale near the finite saddle radius. -/
def fragPermSecondCorrScale (r : ℝ) : ℝ :=
  1 - r

/-- The explicit second-order correction at the saddle radius. -/
def fragPermSecondCorrectionAtSaddle (n : ℕ) : ℝ :=
  saddleCorrection fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
    (fragPermSaddleRadius n)

def fragPermGaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 +
      |x| ^ 11 + |x| ^ 12 + |x| ^ 13 + |x| ^ 14 + |x| ^ 15)

def fragPermLocalTaylorConst : ℝ :=
  100000 * Real.exp 2

def fragPermScaledRemainderConst : ℝ :=
  1000 * fragPermLocalTaylorConst

def fragPermLocalL1Const : ℝ :=
  27 * Real.exp 1 * (20 + fragPermScaledRemainderConst) ^ 3 +
    fragPermScaledRemainderConst +
      6 * (10 + fragPermScaledRemainderConst) * (30 + fragPermScaledRemainderConst)

end FragmentedPermHAdmissible


