-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_UndirectedCycleMarkedPermTuple
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_UndirectedCycleMarkedPermTuple
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:48:41.44001+00:00
-- url     : https://prove2.me/theorems/18952b3b-a1fc-4857-b875-54733bd979ae
-- title:
--   An undirected cycle with a labelled permutation power
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def undirectedCycleMarkedPermTupleClass (k : ℕ) : CombClass :=
--     TwoRegularClass.undirectedCycleClass.lprod (CombClass.permutations.lpow k)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/UndirectedCycleMarkedPermTuple.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledPower
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
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
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
# Undirected-cycle-marked permutation `k`-tuples — the natural remainder at every integer α

This generalizes `UndirectedCycleMarkedPermPairs` (k = 2) to the integer family

  `A k := undirectedCycleClass ⋆ permutations^{⋆k}`,

a `k`-tuple of permutations carrying one distinguished undirected cycle of length ≥ 3,
with EGF

  `(½·log(1/(1-z)) - z/2 - z²/4)·(1-z)^{-k}`
    `= ½·(1-z)^{-k}(-log(1-z)) - (z/2 + z²/4)(1-z)^{-k}`.

For every `k ≥ 2` the residual `-(z/2+z²/4)(1-z)^{-k}` has `‖·‖·‖1-z‖^k → 3/4 ≠ 0`
(strong-remainder transfer fails) but `/log(1/‖1-z‖) → 0` (natural-remainder transfer
applies), giving

  `aₙ / n! ~ ½ · n^{k-1}/(k-1)! · log n`.

So the natural-remainder transfer is needed at *every* integer exponent, not just α = 2.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- A `k`-tuple of permutations with a distinguished undirected cycle (length ≥ 3). -/
def undirectedCycleMarkedPermTupleClass (k : ℕ) : CombClass :=
  TwoRegularClass.undirectedCycleClass.lprod (CombClass.permutations.lpow k)

end AnalyticCombinatorics


