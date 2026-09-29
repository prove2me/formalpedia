-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.weighted_phase_transport
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:39:38.686817+00:00
-- url     : https://prove2.me/submissions/0da34b0d-2285-4cc6-b814-505959236d43

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
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangle
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangleReal
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_StripDecomposition
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftArithmetic
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_PhaseStripDecomposition
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_logb_eq_binary_mul_theta
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Intervals
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
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The printed integer-floor weights and their exact crossing factors. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open scoped BigOperators









theorem triangleTheta_pos {p : ℕ} (hp : 1 < p) : 0 < triangleTheta p := by
  unfold triangleTheta
  exact one_div_pos.mpr (Real.logb_pos (by norm_num) (by exact_mod_cast hp))

theorem phaseFloor_zero_eq_log {p : ℕ} (hp : 1 < p) (a : ℕ) :
    phaseFloor p a 0 = (Nat.log p (2 ^ a) : ℤ) := by
  have hlog : Nat.log p (2 ^ a) = ⌊(a : ℝ) * triangleTheta p⌋₊ := by
    rw [← Real.natFloor_logb_natCast, logb_eq_binary_mul_theta]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  rw [phaseFloor, add_zero, hlog, Int.natCast_floor_eq_floor
    (mul_nonneg (Nat.cast_nonneg a) (triangleTheta_pos hp).le)]

theorem phaseFloor_one_eq_log {p : ℕ} (hp : 1 < p) (a : ℕ) :
    phaseFloor p a 1 = (Nat.log p (2 ^ (a + 1)) : ℤ) := by
  simpa only [phaseFloor, Nat.cast_add, Nat.cast_one, add_zero] using
    phaseFloor_zero_eq_log hp (a + 1)



theorem shiftGamma_eq_floor_powers (a u : ℕ) :
    shiftGamma a u =
      (3 : ℝ) ^ (phaseFloor 3 a 1 + phaseFloor 3 u 0 - phaseFloor 3 (a + u) 1) *
      (5 : ℝ) ^ (phaseFloor 5 a 1 + phaseFloor 5 u 0 - phaseFloor 5 (a + u) 1) := by
  rw [phaseFloor_one_eq_log (by decide : 1 < (3 : ℕ)),
    phaseFloor_zero_eq_log (by decide : 1 < (3 : ℕ)),
    phaseFloor_one_eq_log (by decide : 1 < (3 : ℕ)),
    phaseFloor_one_eq_log (by decide : 1 < (5 : ℕ)),
    phaseFloor_zero_eq_log (by decide : 1 < (5 : ℕ)),
    phaseFloor_one_eq_log (by decide : 1 < (5 : ℕ))]
  simp only [shiftGamma, shiftHeight, threePrimeHeight,
    Nat.log_pow (by decide : 1 < (2 : ℕ))]
  simp only [Nat.cast_mul, Nat.cast_pow,
    zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_sub₀ (by norm_num : (5 : ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_add₀ (by norm_num : (5 : ℝ) ≠ 0),
    zpow_natCast, pow_add, pow_one]
  field_simp
  <;> ring
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution (a u : ℕ) (t : ℝ) :
    shiftGamma a u * phaseOmega (a + u) t = phaseOmega a t * phaseChi a t u := by
  rw [shiftGamma_eq_floor_powers]
  unfold phaseOmega phaseChi phaseCarry
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have h5 : (5 : ℝ) ≠ 0 := by norm_num
  calc
    _ = ((3 : ℝ) ^ (phaseFloor 3 a 1 + phaseFloor 3 u 0 - phaseFloor 3 (a + u) 1) *
          (3 : ℝ) ^ (phaseFloor 3 (a + u) 1 - phaseFloor 3 (a + u) t)) *
        ((5 : ℝ) ^ (phaseFloor 5 a 1 + phaseFloor 5 u 0 - phaseFloor 5 (a + u) 1) *
          (5 : ℝ) ^ (phaseFloor 5 (a + u) 1 - phaseFloor 5 (a + u) t)) := by ring
    _ = ((3 : ℝ) ^ (phaseFloor 3 a 1 - phaseFloor 3 a t) *
          (3 : ℝ) ^ (-(phaseFloor 3 (a + u) t - phaseFloor 3 a t - phaseFloor 3 u 0))) *
        ((5 : ℝ) ^ (phaseFloor 5 a 1 - phaseFloor 5 a t) *
          (5 : ℝ) ^ (-(phaseFloor 5 (a + u) t - phaseFloor 5 a t - phaseFloor 5 u 0))) := by
      rw [← zpow_add₀ h3, ← zpow_add₀ h5, ← zpow_add₀ h3, ← zpow_add₀ h5]
      congr 2 <;> omega
    _ = _ := by ring
