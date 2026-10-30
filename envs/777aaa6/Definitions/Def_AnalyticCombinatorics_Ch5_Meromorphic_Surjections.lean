-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Surjections
-- name    : AnalyticCombinatorics_Ch5_Meromorphic_Surjections
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T20:06:57.391647+00:00
-- url     : https://prove2.me/theorems/e36f02d2-3898-4123-ae02-c5f4893f937c
-- title:
--   Factorial-normalized ordered nonempty-block counts
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def rho : ℂ := ((Real.log 2 : ℝ) : ℂ)
--   ```
--
--   ```lean
--   def surjectionsCount (n : ℕ) : ℕ :=
--     CombClass.posInt.lseq.counts n
--   ```
--
--   ```lean
--   def ofFMLS (p : FormalMultilinearSeries ℂ ℂ ℂ) : PowerSeries ℂ :=
--     PowerSeries.mk fun n => p.coeff n
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/Surjections.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSeq
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Mathlib
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
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


open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Surjections

open AnalyticCombinatorics.Ch1

def rho : ℂ := ((Real.log 2 : ℝ) : ℂ)

def surjEGFℂ : PowerSeries ℂ :=
  PowerSeries.mapℂ CombClass.posInt.lseq.egf

def principal : PowerSeries ℂ :=
  PowerSeries.C ((1 / 2 : ℂ) * rho⁻¹) *
    PowerSeries.rescale rho⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

def remainder : PowerSeries ℂ :=
  surjEGFℂ - principal

namespace PowerSeries

/-- The power series whose coefficients are the scalar coefficients of a formal multilinear
series. -/
def ofFMLS (p : FormalMultilinearSeries ℂ ℂ ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => p.coeff n

end PowerSeries

def expSubOne (z : ℂ) : ℂ :=
  Complex.exp z - 1

def expDiv (z : ℂ) : ℂ :=
  dslope expSubOne 0 z

def expDivSlope (z : ℂ) : ℂ :=
  dslope expDiv 0 z

def analyticRemainderFun (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (expDivSlope (z - rho) / expDiv (z - rho))

def surjAnalyticFun (z : ℂ) : ℂ :=
  (2 - Complex.exp z)⁻¹

def principalAnalyticFun (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (rho - z)⁻¹

def surjectionsCount (n : ℕ) : ℕ :=
  CombClass.posInt.lseq.counts n

end Surjections
end Meromorphic
end Ch5
end AnalyticCombinatorics


