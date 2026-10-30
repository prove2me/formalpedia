-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Secant
-- name    : AnalyticCombinatorics_Ch5_Meromorphic_Secant
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T22:09:05.651956+00:00
-- url     : https://prove2.me/theorems/361af3f0-7c1c-4f02-bac1-6495054e2a3f
-- title:
--   Even secant-number asymptotics
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   abbrev rhoReal : ℝ :=
--     Tangent.rhoReal
--   ```
--
--   ```lean
--   abbrev rho : ℂ :=
--     Tangent.rho
--   ```
--
--   ```lean
--   def secantNumber (n : ℕ) : ℝ :=
--     (n.factorial : ℝ) * (PowerSeries.coeff (R := ℂ) n secantEGFℂ).re
--   ```
--
--   ```lean
--   def secantEGFℂ : PowerSeries ℂ :=
--     Tangent.PowerSeries.ofFMLS (Classical.choose sec_analyticAt_zero)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/Secant.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Tangent
import Mathlib
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
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
import Mathlib.Data.Nat.Fib.Basic
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
namespace Secant

abbrev rhoReal : ℝ :=
  Tangent.rhoReal

abbrev rho : ℂ :=
  Tangent.rho

/-- The principal part with residues `-c` at `rho` and `c` at `-rho`.  In the
`c / (rho - z)` normalization this is `c / (rho - z) - c / (-rho - z)`. -/
def oppositeTwoPolePrincipal (ρ c : ℂ) : PowerSeries ℂ :=
  Tangent.simplePolePrincipal ρ c + Tangent.simplePolePrincipal (-ρ) (-c)

/-- Analytic representative of `oppositeTwoPolePrincipal`. -/
def oppositeTwoPolePrincipalFun (ρ c : ℂ) (z : ℂ) : ℂ :=
  Tangent.simplePolePrincipalFun ρ c z + Tangent.simplePolePrincipalFun (-ρ) (-c) z

theorem sec_analyticAt_zero :
    AnalyticAt ℂ (fun z : ℂ => (Complex.cos z)⁻¹) (0 : ℂ) := by
  have hcos : AnalyticAt ℂ Complex.cos (0 : ℂ) :=
    (Complex.contDiff_cos (n := (⊤ : WithTop ℕ∞))).contDiffAt.analyticAt
  exact hcos.inv (by simp)

/-- The Taylor power series of `sec z = 1 / cos z` at the origin. -/
def secantEGFℂ : PowerSeries ℂ :=
  Tangent.PowerSeries.ofFMLS (Classical.choose sec_analyticAt_zero)

/-- Secant/Euler numbers attached to the real Taylor coefficients of `sec z`. -/
def secantNumber (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * (PowerSeries.coeff (R := ℂ) n secantEGFℂ).re

/-- The formal remainder after subtracting the two dominant secant principal parts. -/
def secantRemainder : PowerSeries ℂ :=
  secantEGFℂ - oppositeTwoPolePrincipal rho (1 : ℂ)

/-- The raw two-pole-subtracted secant function. Its pole values are field defaults; the
removable function below installs analytic values at `±rho`. -/
def secRemRaw (z : ℂ) : ℂ :=
  (Complex.cos z)⁻¹ - (rho - z)⁻¹ - (z + rho)⁻¹

/-- The removable core `(1 / sinDiv w - 1) / w`, analytically defined at `w = 0`. -/
def secPoleCore (w : ℂ) : ℂ :=
  dslope (fun u : ℂ => (Tangent.sinDiv u)⁻¹) 0 w

def secRemLocalPos (z : ℂ) : ℂ :=
  secPoleCore (rho - z) - (z + rho)⁻¹

def secRemLocalNeg (z : ℂ) : ℂ :=
  secPoleCore (z + rho) - (rho - z)⁻¹

/-- The two-pole-subtracted secant function with removable values installed at `±rho`. -/
def secantRemainderFun (z : ℂ) : ℂ :=
  if z = rho then secRemLocalPos z
  else if z = -rho then secRemLocalNeg z
  else secRemRaw z

def knownEvenSecantNumbers : List (ℕ × ℕ) :=
  [(0, 1), (2, 1), (4, 5), (6, 61), (8, 1385)]

def secantAsymptoticScaleReal (n : ℕ) : ℝ :=
  2 * (2 / Real.pi) ^ (n + 1)

def secantRatioCheckReal : List (ℕ × ℝ) :=
  knownEvenSecantNumbers.map fun p =>
    (p.1, (p.2 : ℝ) / ((p.1.factorial : ℝ) * secantAsymptoticScaleReal p.1))

def piFloat : Float :=
  3.141592653589793

def secantAsymptoticScaleFloat (n : ℕ) : Float :=
  2.0 * Float.pow (2.0 / piFloat) (Nat.toFloat (n + 1))

def secantRatioCheckFloat : List (ℕ × Float) :=
  knownEvenSecantNumbers.map fun p =>
    (p.1, p.2.toFloat / (p.1.factorial.toFloat * secantAsymptoticScaleFloat p.1))

end Secant
end Meromorphic
end Ch5
end AnalyticCombinatorics


