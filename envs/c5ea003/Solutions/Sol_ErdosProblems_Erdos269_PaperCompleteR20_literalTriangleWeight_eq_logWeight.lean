-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.literalTriangleWeight_eq_logWeight
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:43:18.920443+00:00
-- url     : https://prove2.me/submissions/e966ddad-5cd4-4269-9806-fb324f291c20

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangle
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangleReal
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_mem_literalTriangle_iff
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_logb_eq_binary_mul_theta
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_log_endpoint_eq_floor_theta
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_triangleLogPoint_eq_log
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_triangleLogPoint_nonneg
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact logarithmic coordinates and the paper's rectangle lower bound. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open scoped BigOperators











theorem floor_triangleLogPoint (v : ℕ × ℕ) :
    ⌊triangleLogPoint v⌋₊ = Nat.log 2 (triangleOddPart v) := by
  rw [triangleLogPoint_eq_log]
  simpa only [Nat.cast_ofNat] using Real.natFloor_logb_natCast 2 (triangleOddPart v)

theorem triangle_lift_log {a : ℕ} {v : ℕ × ℕ} (hv : v ∈ literalTriangle a) :
    Real.logb 2 (smooth3Val 2 3 5 (triangleShellLift a v).1 v.1 v.2) =
      (a : ℝ) + Int.fract (triangleLogPoint v) := by
  have hk : Nat.log 2 (triangleOddPart v) ≤ a := by
    have hm : triangleOddPart v ≠ 0 := by simp [triangleOddPart]
    have := Nat.log_lt_of_lt_pow hm (mem_literalTriangle_iff.mp hv)
    omega
  have hf := Int.floor_add_fract (triangleLogPoint v)
  rw [← natCast_floor_eq_intCast_floor (triangleLogPoint_nonneg v),
    floor_triangleLogPoint] at hf
  simp only [smooth3Val, triangleShellLift, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  push_cast [Nat.cast_sub hk]
  unfold triangleLogPoint at hf ⊢
  linarith



theorem log_lift_eq_floor_phase (p : ℕ) {a : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ literalTriangle a) :
    Nat.log p (smooth3Val 2 3 5 (triangleShellLift a v).1 v.1 v.2) =
      ⌊((a : ℝ) + Int.fract (triangleLogPoint v)) * triangleTheta p⌋₊ := by
  rw [← Real.natFloor_logb_natCast, logb_eq_binary_mul_theta, triangle_lift_log hv]
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution {a : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ literalTriangle a) : literalTriangleWeight a v = literalLogWeight a v := by
  unfold literalTriangleWeight oddHeightSuffix235 literalLogWeight
  change 3 ^ (Nat.log 3 (2 ^ (a + 1)) -
      Nat.log 3 (smooth3Val 2 3 5 (triangleShellLift a v).1 v.1 v.2)) *
    5 ^ (Nat.log 5 (2 ^ (a + 1)) -
      Nat.log 5 (smooth3Val 2 3 5 (triangleShellLift a v).1 v.1 v.2)) = _
  rw [log_endpoint_eq_floor_theta, log_endpoint_eq_floor_theta,
    log_lift_eq_floor_phase 3 hv, log_lift_eq_floor_phase 5 hv]
