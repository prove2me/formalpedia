-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_UndirectedCycleLogSqPermPair
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_UndirectedCycleLogSqPermPair
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:52:34.013995+00:00
-- url     : https://prove2.me/theorems/5c79c7eb-79a5-43c6-9d53-68fc3ae522ea
-- title:
--   An undirected cycle with the source marked permutation pair
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def undirectedCycleLogSqPermPairClass : CombClass :=
--     TwoRegularClass.undirectedCycleClass.lprod cycleMarkedPermPairClass
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/UndirectedCycleLogSqPermPair.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CycleMarkedPermPairs
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularClass
import Mathlib
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Complex.Liouville

namespace AnalyticCombinatorics.Ch5.Meromorphic.Alignments end AnalyticCombinatorics.Ch5.Meromorphic.Alignments

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# A class that GENUINELY needs the natural-remainder log² transfer (~½·n·(log n)²)

`undirectedCycleLogSqPermPairClass := undirectedCycleClass ⋆ cycleMarkedPermPairClass` — an
undirected cycle (length ≥ 3) together with an ordered pair of permutations one of whose cycles is
distinguished — has EGF

  `(½·log(1/(1-z)) - z/2 - z²/4) · log(1/(1-z)) · (1-z)^{-2}`
    `= ½·(1-z)^{-2}·(-log(1-z))²  -  (z/2 + z²/4)·(1-z)^{-2}·(-log(1-z))`.

The residual `R(z) = -(z/2+z²/4)·(1-z)^{-2}·(-log(1-z))` has `‖R‖·‖1-z‖² ≍ |log(1-z)| → ∞`
(so it is NOT `o(|1-z|^{-2})` — the *strong* log² transfer fails), yet
`‖R‖·‖1-z‖²/log²(1/|1-z|) → 0` (so the *natural* log² transfer applies).  Hence

  `aₙ / n! ~ ½·n·(log n)²`.

This is the first class requiring the natural-remainder log² transfer (analog of
`undirectedCycleMarkedPermPairs` for log¹).  (Construction from ChatGPT-Pro ac/ac2.)
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- Undirected cycle ⋆ (pair of permutations with a marked cycle). -/
def undirectedCycleLogSqPermPairClass : CombClass :=
  TwoRegularClass.undirectedCycleClass.lprod cycleMarkedPermPairClass

/-! ### This class genuinely NEEDS the natural transfer: the strong log² remainder fails.
Along the real radial path `z = 1 - 1/(n+2) → 1`, `‖R(z)‖·‖1-z‖² = ‖z/2+z²/4‖·log(n+2) → ∞`,
so `R` is not `o(|1-z|^{-2})` — the strong-remainder log² transfer cannot apply. -/

end AnalyticCombinatorics


