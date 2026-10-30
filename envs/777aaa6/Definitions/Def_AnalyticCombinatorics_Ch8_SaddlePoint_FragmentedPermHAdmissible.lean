-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:35:33.543396+00:00
-- url     : https://prove2.me/theorems/d17d3aac-1fd2-4a01-a9e6-45c21e86567e
-- title:
--   Fragmented Perm H Admissible
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   def fragPermCarrier : PowerSeries ℂ :=
--     (PowerSeries.exp ℂ).subst fragPermInnerPS
--   ```
--
--   ```lean
--   noncomputable abbrev fragPermSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
--     PowerSeries.toFMLS fragPermCarrier
--   ```
--
--   ```lean
--   def fragPermSaddleRadius (n : ℕ) : ℝ :=
--     1 - 2 / (Real.sqrt (4 * (n : ℝ) + 1) + 1)
--   ```
--
--   ```lean
--   abbrev fragPermFun (z : ℂ) : ℂ :=
--     Complex.exp (z / (1 - z))
--   ```
--
--   ```lean
--   def fragPermInnerPS : PowerSeries ℂ :=
--     (PowerSeries.X : PowerSeries ℂ) * PowerSeries.pole1
--   ```
--
--   ```lean
--   def fragPermSaddleBReal (r : ℝ) : ℝ :=
--     r * (1 + r) / (1 - r) ^ 3
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermHAdmissible.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
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
# Fragmented permutations: finite-radius H-admissible saddle data

Fragmented permutations are the labelled class `SET(SEQ_{\ge 1}(Z))`, with EGF
`exp (z / (1 - z))`.  This file packages the finite-radius Hayman data for the
committed `HAdmissible` bridge.  The saddle regime is `r -> 1-`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace FragmentedPermHAdmissible

/-- The fragmented-permutation EGF, `exp (z/(1-z))`. -/
abbrev fragPermFun (z : ℂ) : ℂ :=
  Complex.exp (z / (1 - z))

/-- The rational exponent `h(z)=z/(1-z)`. -/
abbrev fragPermH (z : ℂ) : ℂ :=
  z / (1 - z)

/-- The inner series `z + z^2 + ...`, represented as `X/(1-X)`. -/
def fragPermInnerPS : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) * PowerSeries.pole1

/-- The formal EGF carrier `exp (X/(1-X))`. -/
def fragPermCarrier : PowerSeries ℂ :=
  (PowerSeries.exp ℂ).subst fragPermInnerPS

/-- The formal series used by the H-admissible interface. -/
noncomputable abbrev fragPermSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS fragPermCarrier

/-- The radius filter `r -> 1-`. -/
def fragPermRadFilter : Filter ℝ :=
  𝓝[Set.Iio (1 : ℝ)] (1 : ℝ)

/-- Continuous saddle mean, `a(r)=r/(1-r)^2`. -/
def fragPermSaddleAReal (r : ℝ) : ℝ :=
  r / (1 - r) ^ 2

/-- Continuous saddle variance scale, `b(r)=r(1+r)/(1-r)^3`. -/
def fragPermSaddleBReal (r : ℝ) : ℝ :=
  r * (1 + r) / (1 - r) ^ 3

/-- Hayman window.  The exponent lies in `(4/3, 3/2)`. -/
def fragPermSaddleDeltaReal (r : ℝ) : ℝ :=
  (1 - r) ^ (7 / 5 : ℝ)

/-- Tail ratio constant from the flat-envelope real-part estimate. -/
def fragPermTailRatioC : ℝ :=
  1 / (3 * Real.pi ^ 2)

/-- Exponential tail decay constant after substituting `b(r) δ(r)^2`. -/
def fragPermTailC : ℝ :=
  1 / (4 * Real.pi ^ 2)

/-- Flat-envelope tail bound. -/
def fragPermTailE (r : ℝ) : ℝ :=
  Real.exp (-fragPermTailC * (1 - r) ^ (-(1 / 5 : ℝ)))

@[simp] lemma fragPermSaddleAReal_apply (r : ℝ) :
    fragPermSaddleAReal r = r / (1 - r) ^ 2 := rfl

@[simp] lemma fragPermSaddleBReal_apply (r : ℝ) :
    fragPermSaddleBReal r = r * (1 + r) / (1 - r) ^ 3 := rfl

@[simp] lemma fragPermSaddleDeltaReal_apply (r : ℝ) :
    fragPermSaddleDeltaReal r = (1 - r) ^ (7 / 5 : ℝ) := rfl

@[simp] lemma fragPermTailRatioC_apply :
    fragPermTailRatioC = 1 / (3 * Real.pi ^ 2) := rfl

@[simp] lemma fragPermTailC_apply :
    fragPermTailC = 1 / (4 * Real.pi ^ 2) := rfl

/-- The exact exponent left after removing the linear and quadratic saddle terms. -/
def fragPermLocalExponent (r θ : ℝ) : ℂ :=
  fragPermH ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) -
    fragPermH (r : ℂ) -
      ((fragPermSaddleAReal r * θ : ℝ) : ℂ) * Complex.I +
        ((fragPermSaddleBReal r * θ ^ 2 / 2 : ℝ) : ℂ)

def fragPermLocalConstant : ℝ :=
  100 * Real.exp 1

/-- Explicit saddle radius solving `r/(1-r)^2=n`. -/
def fragPermSaddleRadius (n : ℕ) : ℝ :=
  1 - 2 / (Real.sqrt (4 * (n : ℝ) + 1) + 1)

end FragmentedPermHAdmissible


