-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperR10_height_growth_sharp_dyadic
-- name    : ErdosProblems.Erdos269.PaperR10.height_growth_sharp_dyadic
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:54:35.702216+00:00
-- url     : https://prove2.me/theorems/bf6c2fab-6d48-4e21-af73-a3f475fc7443
-- title:
--   Height growth sharp dyadic
-- statement:
--   For x≥2^a, height growth from 2^a to x dominates the sharp jump denominator at the difference of height ranks.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/ActualSharpTailMajorantR10.lean#L66-L120
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
import Definitions.Def_ErdosProblems_Erdos269_PaperR8RankMajorant
import Definitions.Def_ErdosProblems_Erdos269_ActualSharpTailMajorantR10
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace PaperR7
end PaperR7

namespace PaperR8
end PaperR8

/-!
# The jump-constrained bound for the literal tail

The extra growth is proved directly for the three floor logarithms. This avoids
assuming an enumeration of the jump word or an unproved majorisation supplier.
At a dyadic starting point, d₂ ≤ 2d₃+1. Consequently the first k rank increases
multiply the height by at least 2^(k-j)3^j, j=(k+1)/3. The residue-three sum
then gives precisely the printed Q̃, with the existing actual rank-fibre bound.


-/


open scoped BigOperators
open PaperR7 PaperR8

open ErdosProblems.Erdos269.PaperR10

open ErdosProblems.Erdos269.PaperR7
open ErdosProblems.Erdos269.PaperR8

theorem ErdosProblems.Erdos269.PaperR10.height_growth_sharp_dyadic (a x : ℕ) (hx : 2 ^ a ≤ x) :
    threePrimeHeight 2 3 5 (2 ^ a) *
      sharpJumpDenom (heightRank235 x - paperJumpIndex a) ≤
        threePrimeHeight 2 3 5 x := by sorry
