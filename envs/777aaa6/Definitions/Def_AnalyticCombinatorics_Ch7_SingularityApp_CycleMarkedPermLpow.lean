-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CycleMarkedPermLpow
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_CycleMarkedPermLpow
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:51:38.781783+00:00
-- url     : https://prove2.me/theorems/a04c329d-c5af-46a1-91d7-d1e15b0d0577
-- title:
--   Cycle Marked Perm Lpow
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   noncomputable def cycleMarkedPermLpowClass (k : ℕ) : CombClass :=
--     cycleMarkedPermClass.lpow k
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/CycleMarkedPermLpow.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledPower
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CycleMarkedPermPairs
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# A genuine logᵏ combinatorial application (`~ n^{k-1}/(k-1)!·(log n)ᵏ`)

`cycleMarkedPermLpowClass k := cycleMarkedPermClass.lpow k` — an ordered `k`-tuple of
permutations, each with one distinguished cycle — has EGF

  `(log(1/(1-z))·(1-z)^{-1})^k = log^k(1/(1-z))·(1-z)^{-k} = logKSingularityFun k k`.

Applying the general logᵏ transfer at `α = k`, `C = 1` (zero residual) gives

  `aₙ / n! ~ n^{k-1}/(k-1)!·(log n)ᵏ`   (for `k ≥ 2`),

the first end-to-end use of the general logᵏ singularity hierarchy.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1

/-- Ordered `k`-tuple of marked-cycle permutations. -/
noncomputable def cycleMarkedPermLpowClass (k : ℕ) : CombClass :=
  cycleMarkedPermClass.lpow k

end AnalyticCombinatorics


