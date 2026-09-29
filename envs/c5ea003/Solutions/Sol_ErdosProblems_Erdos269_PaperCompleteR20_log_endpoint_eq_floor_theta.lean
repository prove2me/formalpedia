-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.log_endpoint_eq_floor_theta
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:39:12.801177+00:00
-- url     : https://prove2.me/submissions/d37120e0-4b62-4552-8d0a-339348b691bb

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_logb_eq_binary_mul_theta
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
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution (p a : ℕ) :
    Nat.log p (2 ^ (a + 1)) = ⌊((a : ℝ) + 1) * triangleTheta p⌋₊ := by
  rw [← Real.natFloor_logb_natCast, logb_eq_binary_mul_theta]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one, Nat.cast_add, Nat.cast_one]
