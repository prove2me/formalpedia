-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Tangent
-- name    : AnalyticCombinatorics_Ch5_Meromorphic_Tangent
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T22:07:18.721989+00:00
-- url     : https://prove2.me/theorems/e7b30a8a-fbcc-42c0-8b5f-c6031e1de6b1
-- title:
--   Tangent
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def rhoReal : ℝ :=
--     Real.pi / 2
--   ```
--
--   ```lean
--   def rho : ℂ :=
--     (rhoReal : ℂ)
--   ```
--
--   ```lean
--   def tangentNumberReal (n : ℕ) : ℝ :=
--     (n.factorial : ℝ) * (PowerSeries.coeff (R := ℂ) n tangentEGFℂ).re
--   ```
--
--   ```lean
--   def ofFMLS (p : FormalMultilinearSeries ℂ ℂ ℂ) : PowerSeries ℂ :=
--     PowerSeries.mk fun n => p.coeff n
--   ```
--
--   ```lean
--   def tangentEGFℂ : PowerSeries ℂ :=
--     PowerSeries.ofFMLS (Classical.choose tan_analyticAt_zero)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/Tangent.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Tangent

namespace PowerSeries

/-- The power series whose coefficients are the scalar coefficients of a formal multilinear
series.  This local bridge is used to package the Taylor series obtained from `AnalyticAt`. -/
def ofFMLS (p : FormalMultilinearSeries ℂ ℂ ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => p.coeff n

end PowerSeries

/-- The positive dominant pole radius `π / 2`. -/
def rhoReal : ℝ :=
  Real.pi / 2

/-- The positive dominant pole of `tan`. -/
def rho : ℂ :=
  (rhoReal : ℂ)

/-- A single simple-pole principal part `c / (ρ - z)`. -/
def simplePolePrincipal (ρ c : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (c * ρ⁻¹) *
    PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

/-- The symmetric two-pole principal part `c / (ρ - z) + c / (-ρ - z)`. -/
def twoPolePrincipal (ρ c : ℂ) : PowerSeries ℂ :=
  simplePolePrincipal ρ c + simplePolePrincipal (-ρ) c

theorem tan_analyticAt_zero : AnalyticAt ℂ Complex.tan (0 : ℂ) := by
  have hcos : Complex.cos (0 : ℂ) ≠ 0 := by simp
  exact ((Complex.contDiffAt_tan (x := (0 : ℂ)) (n := (⊤ : WithTop ℕ∞))).2 hcos).analyticAt

/-- The Taylor power series of `Complex.tan` at the origin. -/
def tangentEGFℂ : PowerSeries ℂ :=
  PowerSeries.ofFMLS (Classical.choose tan_analyticAt_zero)

/-- Tangent numbers, represented by their exponential generating function coefficients.
Thus `tangentNumber n / n! = [z^n] tan z` by definition. -/
def tangentNumber (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff (R := ℂ) n tangentEGFℂ

/-- The formal remainder after subtracting the two dominant tangent principal parts. -/
def tangentRemainder : PowerSeries ℂ :=
  tangentEGFℂ - twoPolePrincipal rho (1 : ℂ)

/-- Analytic function represented by a single simple-pole principal part near the origin. -/
def simplePolePrincipalFun (ρ c : ℂ) (z : ℂ) : ℂ :=
  c * (ρ - z)⁻¹

/-- Analytic function represented by the symmetric two-pole principal part near the origin. -/
def twoPolePrincipalFun (ρ c : ℂ) (z : ℂ) : ℂ :=
  simplePolePrincipalFun ρ c z + simplePolePrincipalFun (-ρ) c z

/-- The raw two-pole-subtracted tangent function.  Its values at the two poles are the
field-default values, so `tangentRemainderFun` below replaces them by the removable limits. -/
def tanRemRaw (z : ℂ) : ℂ :=
  Complex.tan z + (z - rho)⁻¹ + (z + rho)⁻¹

/-- `sin z / z`, with the removable value at zero. -/
def sinDiv (z : ℂ) : ℂ :=
  dslope Complex.sin 0 z

/-- The removable core `cot w - 1 / w`, defined analytically at `w = 0`. -/
def tanPoleCore (w : ℂ) : ℂ :=
  dslope (fun u : ℂ => Complex.cos u - sinDiv u) 0 w / sinDiv w

def tanRemLocalPos (z : ℂ) : ℂ :=
  tanPoleCore (rho - z) + (z + rho)⁻¹

def tanRemLocalNeg (z : ℂ) : ℂ :=
  -tanPoleCore (z + rho) + (z - rho)⁻¹

/-- The two-pole-subtracted tangent function with the removable values installed at `±ρ`. -/
def tangentRemainderFun (z : ℂ) : ℂ :=
  if z = rho then tanRemLocalPos z
  else if z = -rho then tanRemLocalNeg z
  else tanRemRaw z

/-- Real tangent numbers attached to the real Taylor coefficients of `tan`. -/
def tangentNumberReal (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * (PowerSeries.coeff (R := ℂ) n tangentEGFℂ).re

def knownOddTangentNumbers : List (ℕ × ℕ) :=
  [(1, 1), (3, 2), (5, 16), (7, 272), (9, 7936)]

def tangentAsymptoticScaleReal (n : ℕ) : ℝ :=
  2 * (2 / Real.pi) ^ (n + 1)

def tangentRatioCheckReal : List (ℕ × ℝ) :=
  knownOddTangentNumbers.map fun p =>
    (p.1, (p.2 : ℝ) / ((p.1.factorial : ℝ) * tangentAsymptoticScaleReal p.1))

def piFloat : Float :=
  3.141592653589793

def tangentAsymptoticScaleFloat (n : ℕ) : Float :=
  2.0 * Float.pow (2.0 / piFloat) (Nat.toFloat (n + 1))

def tangentRatioCheckFloat : List (ℕ × Float) :=
  knownOddTangentNumbers.map fun p =>
    (p.1, p.2.toFloat / (p.1.factorial.toFloat * tangentAsymptoticScaleFloat p.1))

end Tangent
end Meromorphic
end Ch5
end AnalyticCombinatorics


