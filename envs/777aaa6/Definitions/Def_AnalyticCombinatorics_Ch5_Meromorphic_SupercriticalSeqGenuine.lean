-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_SupercriticalSeqGenuine
-- name    : AnalyticCombinatorics_Ch5_Meromorphic_SupercriticalSeqGenuine
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T15:33:15.488985+00:00
-- url     : https://prove2.me/theorems/31bdd6c3-9474-44a5-a170-a65891761662
-- title:
--   Analytic division and a removable simple-pole remainder
-- statement:
--   shiftedC moves a complex point rho to zero. cdiv is its divided difference at zero, using the derivative value at zero; cdivSlope repeats this construction. remainderFun divides cdivSlope by Cderiv times cdiv. principalSeries rho c is the formal geometric series with coefficient c times rho inverse to the power n+1, and principalFun is c/(rho-z). These definitions are totalized, including zero denominators. Conditions making them analytic principal parts or a removable remainder belong to separate theorems.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/SupercriticalSeqGenuine.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
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

namespace SupercriticalSeqGenuine

/-- Shift `C` so that the candidate singularity is at the origin. -/
def shiftedC (Cfun : ℂ → ℂ) (ρ : ℂ) (w : ℂ) : ℂ :=
  Cfun (ρ + w)

/-- The divided difference `(C(ρ+w)-C(ρ))/w`, with the derivative value at `w=0`. -/
def cdiv (Cfun : ℂ → ℂ) (ρ : ℂ) (w : ℂ) : ℂ :=
  dslope (shiftedC Cfun ρ) 0 w

/-- The divided difference of `cdiv`; this is the analytic numerator left after the pole is
subtracted. -/
def cdivSlope (Cfun : ℂ → ℂ) (ρ : ℂ) (w : ℂ) : ℂ :=
  dslope (cdiv Cfun ρ) 0 w

/-- The removable remainder after subtracting `(1/C'(ρ))/(ρ-z)` from `1/(1-C(z))`. -/
def remainderFun (Cfun : ℂ → ℂ) (ρ Cderiv : ℂ) (z : ℂ) : ℂ :=
  cdivSlope Cfun ρ (z - ρ) / (Cderiv * cdiv Cfun ρ (z - ρ))

/-- Formal simple-pole principal part with analytic function `c/(ρ-z)`. -/
def principalSeries (ρ c : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (c * ρ⁻¹) *
    PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

/-- The analytic function represented at the origin by `principalSeries ρ c`. -/
def principalFun (ρ c : ℂ) (z : ℂ) : ℂ :=
  c * (ρ - z)⁻¹

end SupercriticalSeqGenuine

end Meromorphic
end Ch5
end AnalyticCombinatorics


