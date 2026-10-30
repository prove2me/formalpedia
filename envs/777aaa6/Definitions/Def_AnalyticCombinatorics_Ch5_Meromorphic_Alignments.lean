-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Alignments
-- name    : AnalyticCombinatorics_Ch5_Meromorphic_Alignments
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T21:19:47.22146+00:00
-- url     : https://prove2.me/theorems/fa6a6dbe-af55-4d06-8ec1-a24963930ac0
-- title:
--   Factorial-normalized alignment counts
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def alignmentClass : CombClass :=
--     CombClass.atom.lcyc.lseq
--   ```
--
--   ```lean
--   def alignmentCount (n : ℕ) : ℕ :=
--     alignmentClass.counts n
--   ```
--
--   ```lean
--   def rho : ℂ :=
--     (rhoReal : ℂ)
--   ```
--
--   ```lean
--   def alignmentConstant : ℂ :=
--     ((((Real.exp 1 - 1)⁻¹ : ℝ)) : ℂ)
--   ```
--
--   ```lean
--   def rhoReal : ℝ :=
--     1 - (Real.exp 1)⁻¹
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/Alignments.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Mathlib
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Alignments

open AnalyticCombinatorics.Ch1

/-- The genuine labelled class of alignments: `SEQ(CYC(Z))`. -/
def alignmentClass : CombClass :=
  CombClass.atom.lcyc.lseq

/-- The alignment numbers `o_n`. This is a genuine labelled combinatorial definition. -/
def alignmentCount (n : ℕ) : ℕ :=
  alignmentClass.counts n

/-- The real dominant singularity `rho = 1 - 1 / e`. -/
def rhoReal : ℝ :=
  1 - (Real.exp 1)⁻¹

/-- The dominant singularity as a complex number. -/
def rho : ℂ :=
  (rhoReal : ℂ)

/-- The simple-pole numerator `c = 1 / L'(rho) = 1 / e`, for
`1 / (1 - L(z)) ~ c / (rho - z)`. -/
def poleNumerator : ℂ :=
  (((Real.exp 1)⁻¹ : ℝ) : ℂ)

/-- The coefficient-asymptotic constant in the normalization
`[z^n] O(z) ~ C * rho^{-n}`. -/
def alignmentConstant : ℂ :=
  ((((Real.exp 1 - 1)⁻¹ : ℝ)) : ℂ)

/-- The formal power series for `log (1 / (1 - z))`, with zero constant term. -/
def cycleEGFℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n : ℕ => ((n : ℂ)⁻¹)

/-- The same formal logarithm over `ℚ`, used to identify the genuine `CYC(Z)` EGF. -/
def cycleEGFℚ : PowerSeries ℚ :=
  PowerSeries.mk fun n : ℕ => ((n : ℚ)⁻¹)

/-- The complex EGF of the genuine alignment class. -/
def alignmentEGFℂ : PowerSeries ℂ :=
  PowerSeries.mapℂ alignmentClass.egf

/-- The dominant simple-pole principal part. -/
def principal : PowerSeries ℂ :=
  PowerSeries.C (poleNumerator * rho⁻¹) *
    PowerSeries.rescale rho⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

/-- The analytic remainder after removing the dominant pole. -/
def remainder : PowerSeries ℂ :=
  alignmentEGFℂ - principal

/-- Analytic representative of the labelled-cycle EGF `log (1 / (1 - z))`
on the principal branch. -/
def cycleAnalyticFun (z : ℂ) : ℂ :=
  -Complex.log (1 - z)

/-- Analytic representative of the alignment EGF away from the zeros of
`1 - cycleAnalyticFun`. -/
def alignmentAnalyticFun (z : ℂ) : ℂ :=
  (1 - cycleAnalyticFun z)⁻¹

/-- Analytic representative of the dominant principal part. -/
def principalAnalyticFun (z : ℂ) : ℂ :=
  poleNumerator * (rho - z)⁻¹

/-- The shifted cycle EGF `w ↦ L(rho + w)`. -/
def shiftedCycleAnalyticFun (w : ℂ) : ℂ :=
  cycleAnalyticFun (rho + w)

/-- The divided difference `(L(rho+w)-L(rho))/w`, extended at `w=0` by the derivative. -/
def cycleDiv (w : ℂ) : ℂ :=
  dslope shiftedCycleAnalyticFun 0 w

/-- The divided difference `(cycleDiv w - cycleDiv 0)/w`, again extended at `0`. -/
def cycleDivSlope (w : ℂ) : ℂ :=
  dslope cycleDiv 0 w

/-- The removable analytic continuation of `alignmentAnalyticFun - principalAnalyticFun`
across `z = rho`. -/
def analyticRemainderFun (z : ℂ) : ℂ :=
  cycleDivSlope (z - rho) / (((Real.exp 1 : ℝ) : ℂ) * cycleDiv (z - rho))

end Alignments
end Meromorphic
end Ch5
end AnalyticCombinatorics


