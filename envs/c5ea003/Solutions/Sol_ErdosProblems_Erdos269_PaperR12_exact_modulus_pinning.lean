-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR12.exact_modulus_pinning
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:57:18.41798+00:00
-- url     : https://prove2.me/submissions/952ce558-a506-4b3c-82c0-7e72186ba30a

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

namespace ErdosProblems.Erdos269.PaperR12
open PaperR7 Filter
open scoped Topology
end ErdosProblems.Erdos269.PaperR12

open PaperR7 Filter
open scoped Topology
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR12 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution {x y K : ℝ} {W F r : ℤ}
    (hW : 0 < W) (hwin : y = (W : ℝ) * x - (F : ℝ))
    (hcong : W ∣ F + r)
    (hy0 : 0 ≤ y) (hyK : y ≤ K)
    (hr0 : (0 : ℝ) ≤ r) (hrK : (r : ℝ) ≤ K) :
    ∃ k : ℤ, |x - (k : ℝ)| ≤ K / (W : ℝ) := by
  obtain ⟨k, hk⟩ := hcong
  have hkR : (F : ℝ) + (r : ℝ) = (W : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  have hkey : (W : ℝ) * (x - (k : ℝ)) = y - (r : ℝ) := by
    nlinarith only [hwin, hkR]
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have ha : |y - (r : ℝ)| ≤ K := by
    exact abs_le.2 ⟨by linarith, by linarith⟩
  refine ⟨k, (le_div_iff₀ hWR).2 ?_⟩
  calc
    |x - (k : ℝ)| * (W : ℝ) = |(W : ℝ) * (x - (k : ℝ))| := by
      rw [abs_mul, abs_of_pos hWR, mul_comm]
    _ = |y - (r : ℝ)| := by rw [hkey]
    _ ≤ K := ha
