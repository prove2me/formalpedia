-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CycleMarkedPermPairs
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_CycleMarkedPermPairs
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:50:11.842588+00:00
-- url     : https://prove2.me/theorems/c28391f1-6736-4c75-abd3-ad08646ba713
-- title:
--   Cycle Marked Perm Pairs
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def cycleMarkedPermClass : CombClass :=
--     CombClass.atom.lcyc.lprod CombClass.permutations
--   ```
--
--   ```lean
--   def cycleMarkedPermPairClass : CombClass :=
--     cycleMarkedPermClass.lprod CombClass.permutations
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/CycleMarkedPermPairs.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Mathlib
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Complex.Liouville

namespace AnalyticCombinatorics.Ch5.Meromorphic.Alignments end AnalyticCombinatorics.Ch5.Meromorphic.Alignments

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# A genuine labelled class with an `n log n` coefficient asymptotic

The labelled class

  `cycleMarkedPermPairClass := (CYC ⋆ SET(CYC)) ⋆ SET(CYC)`

— an ordered pair of permutations in which one cycle of the first permutation is
distinguished — has exponential generating function

  `A(z) = log(1/(1-z)) · 1/(1-z)² = (1-z)^{-2} · (-log(1-z))`,

which is exactly the logarithmic-singularity model `logSingularityFun 2`.  By the
unconditional strong-remainder logarithmic transfer
(`log_transfer_theorem_strong_remainder_unconditional`) at the clean point
`α = 2`, `C = 1`, with *zero* singular remainder, its normalized coefficients
satisfy

  `aₙ / n! ~ n · log n`   (since `Γ(2) = 1`).

This is the first application of the new unconditional log transfer to a genuine
labelled species.  All the analysis is banked: the only new work is
labelled-class / EGF plumbing, which reduces to the formal identity
`mapℂ A.egf = logSingularityGF 2`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- A permutation with one distinguished cycle: a single labelled cycle (`atom.lcyc`)
attached to an arbitrary permutation of the remaining labels.  EGF `log(1/(1-z))·1/(1-z)`. -/
def cycleMarkedPermClass : CombClass :=
  CombClass.atom.lcyc.lprod CombClass.permutations

/-- An ordered pair: a cycle-marked permutation together with a second permutation.
EGF `log(1/(1-z))·1/(1-z)² = (1-z)^{-2}·(-log(1-z))`. -/
def cycleMarkedPermPairClass : CombClass :=
  cycleMarkedPermClass.lprod CombClass.permutations

/-! ### Formal EGF identity `mapℂ A.egf = logSingularityGF 2` -/

/-! ### The `n log n` coefficient asymptotic via the unconditional log transfer -/

end AnalyticCombinatorics


