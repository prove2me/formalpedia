-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftValue
-- name    : ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftValue
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:19:39.913421+00:00
-- url     : https://prove2.me/theorems/f1a0a0a9-dae5-467f-a06a-9d4070d43edf
-- title:
--   WeightedShiftValue
-- statement:
--   Defines the shifted series term, integer leading coefficient, finite prefix correction, and quadratic coefficient norm used in weighted-shift estimates.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/WeightedShiftValue.lean#L1-L244
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_JumpConstraintMajorant
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Definitions.Def_ErdosProblems_Erdos269_PaperR7SeriesIdentification
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Definitions.Def_ErdosProblems_Erdos269_RationalityCarryBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7RationalBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7WindowResults
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftArithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

-- `Summable.norm` (the alias of `summable_norm_iff`) no longer arrives transitively on Lean 4.30.0
-- / Mathlib c5ea0035, and dot notation no longer resolves it because `Summable` now unfolds to
-- `Exists`. Imported explicitly and applied by name below. Statements are unchanged.
/-!
# Weighted shifts of the literal series

Finite linear combinations of shifted digits retain the original value
with an integer prefix correction. All sums below converge absolutely.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7
open scoped BigOperators

noncomputable def shiftTerm (a : ℕ) : ℝ :=
  (dyadicOrderedBlockDigit235 a : ℝ) / (shiftHeight (a + 1) : ℝ)









def shiftedLeading (c : ℕ → ℤ) (σ r : ℕ) : ℤ :=
  15 * ∑ j ∈ Finset.range (σ + 1), c j * (shiftHeight (j * r) : ℤ)

noncomputable def shiftedCorrection (c : ℕ → ℤ) (σ r : ℕ) : ℝ :=
  15 * ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * shiftedPrefix (j * r)







noncomputable def shiftedQuadraticConstant (c : ℕ → ℤ) (σ : ℕ) : ℝ :=
  225 * ∑ j ∈ Finset.range (σ + 1), |(c j : ℝ)| * (max 1 j : ℝ) ^ 2














end ErdosProblems.Erdos269.PaperCompleteR20


