-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.eight_pow_lt_fifteen_dyadic_height
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:02:18.173203+00:00
-- url     : https://prove2.me/submissions/c13a163f-6852-4a11-9fc6-67f754ad9381

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_eight_pow_eq_two_pow_cube
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

/-!
# Round 7: exact window statements at the correct bounds

The short cap is `90 B (a+1)^2`. The long cap is `floor(B Q(n_a))`.
They are separately named. No validity claim about the latter is inferred from
the former. The bounded-length obstruction needs only growth of the long cap,
so it can be proved without assuming the unresolved `X_a <= Q(n_a)` bridge.

No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7
open scoped BigOperators
end ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (a : ℕ) :
    (8 : ℝ) ^ a < 15 * (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) := by
  have h3 := Nat.lt_pow_succ_log_self (b := 3) (by norm_num) (2 ^ a)
  have h5 := Nat.lt_pow_succ_log_self (b := 5) (by norm_num) (2 ^ a)
  have h35 := Nat.mul_lt_mul_of_lt_of_lt h3 h5
  have hp : (0 : ℕ) < 2 ^ a := by positivity
  have hmul := Nat.mul_lt_mul_of_pos_left h35 hp
  have hnat : (8 : ℕ) ^ a < 15 * threePrimeHeight 2 3 5 (2 ^ a) := by
    calc
      (8 : ℕ) ^ a = 2 ^ a * (2 ^ a * 2 ^ a) := by
        rw [eight_pow_eq_two_pow_cube]
        ring
      _ < 2 ^ a * (3 ^ (Nat.log 3 (2 ^ a) + 1) *
          5 ^ (Nat.log 5 (2 ^ a) + 1)) := hmul
      _ = 15 * threePrimeHeight 2 3 5 (2 ^ a) := by
        simp only [threePrimeHeight, Nat.log_pow (by norm_num : 1 < (2 : ℕ)), pow_succ]
        ring
  exact_mod_cast hnat
