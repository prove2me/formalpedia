-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_FibonacciCompositions
-- name    : AnalyticCombinatorics_Ch5_Meromorphic_FibonacciCompositions
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T15:33:14.634845+00:00
-- url     : https://prove2.me/theorems/b1f3ffed-16af-486a-95f9-b2f0ae07de07
-- title:
--   Fibonacci compositions and their principal parts
-- statement:
--   The sequence fibonacciCompositionCount(n) is defined as Nat.fib(n+1). Its formal coefficient series and the formal inverse of 1-X-X² are supplied separately. The roots rho=(sqrt(5)-1)/2 and otherRoot=-goldenRatio, with constants 1/sqrt(5) and -1/sqrt(5), define two geometric principal parts; remainder is the second principal part. These definitions use the shifted Fibonacci sequence directly; a separate list-cardinality interpretation is not built into the count definition.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/FibonacciCompositions.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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


/-!
# Fibonacci compositions via the meromorphic transfer

Compositions of `n` into parts `1` and `2` are represented here by the shifted
Fibonacci count `Nat.fib (n + 1)`.  The ordinary generating function is
`1 / (1 - z - z^2)`, whose dominant pole is
`rho = (sqrt 5 - 1) / 2`.
-/

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace FibonacciCompositionsNS

local notation "φc" => ((Real.goldenRatio : ℝ) : ℂ)
local notation "ψc" => ((Real.goldenConj : ℝ) : ℂ)
local notation "√5c" => ((Real.sqrt 5 : ℝ) : ℂ)

/-- The dominant pole `rho = (sqrt 5 - 1) / 2 = 1 / phi`. -/
def rho : ℂ := (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ)

/-- The other pole, `-phi`. -/
def otherRoot : ℂ := ((-Real.goldenRatio : ℝ) : ℂ)

/-- The shifted Fibonacci count for `{1,2}`-compositions. -/
def fibonacciCompositionCount (n : ℕ) : ℕ := Nat.fib (n + 1)

/-- The formal power series with coefficients `F_{n+1}`. -/
def fibonacciSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (fibonacciCompositionCount n : ℂ)

/-- The rational OGF `1 / (1 - z - z^2)`. -/
def fibonacciOGFℂ : PowerSeries ℂ :=
  (1 - (PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℂ)⁻¹

/-- The `c = -residue` constant at the dominant pole. -/
def dominantResidueConstant : ℂ := √5c⁻¹

/-- The `c = -residue` constant at the conjugate pole. -/
def conjugateResidueConstant : ℂ := -√5c⁻¹

/-- Principal part at the dominant pole in the normalization used by
`dominant_simplePole_isEquivalent`. -/
def dominantPrincipal : PowerSeries ℂ :=
  PowerSeries.C (dominantResidueConstant * rho⁻¹) *
    PowerSeries.rescale rho⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

/-- The non-dominant simple-pole contribution. -/
def conjugatePrincipal : PowerSeries ℂ :=
  PowerSeries.C (conjugateResidueConstant * otherRoot⁻¹) *
    PowerSeries.rescale otherRoot⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

/-- The analytic remainder past the dominant pole. -/
def remainder : PowerSeries ℂ := conjugatePrincipal

end FibonacciCompositionsNS
end Meromorphic
end Ch5
end AnalyticCombinatorics


