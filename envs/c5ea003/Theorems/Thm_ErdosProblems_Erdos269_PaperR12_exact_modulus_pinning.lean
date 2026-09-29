-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperR12_exact_modulus_pinning
-- name    : ErdosProblems.Erdos269.PaperR12.exact_modulus_pinning
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:57:07.610561+00:00
-- url     : https://prove2.me/theorems/c7cc6487-05cc-4c27-bd94-923523e9e0a5
-- title:
--   Exact modulus pinning
-- statement:
--   Under positive modulus W and bounded nonnegative terminal state and residue, a congruence pins the starting state within K/W of an integer.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/R12/ExactModulus.lean#L43-L64
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
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace ErdosProblems.Erdos269.PaperR12
end ErdosProblems.Erdos269.PaperR12

namespace PaperR7
end PaperR7

/-!
# Exact-modulus pinning and eventual escape at a fixed start

The precise denominator is the actual window product, not its lower bound
2^len. A nonintegral real (even a nonintegral rational) is separated from the
integers. This yields eventual escape when the relative bound tends to zero.

-/
open PaperR7 Filter
open scoped Topology

open ErdosProblems.Erdos269.PaperR12

open ErdosProblems.Erdos269.PaperR7

theorem ErdosProblems.Erdos269.PaperR12.exact_modulus_pinning {x y K : ℝ} {W F r : ℤ}
    (hW : 0 < W) (hwin : y = (W : ℝ) * x - (F : ℝ))
    (hcong : W ∣ F + r)
    (hy0 : 0 ≤ y) (hyK : y ≤ K)
    (hr0 : (0 : ℝ) ≤ r) (hrK : (r : ℝ) ≤ K) :
    ∃ k : ℤ, |x - (k : ℝ)| ≤ K / (W : ℝ) := by sorry
