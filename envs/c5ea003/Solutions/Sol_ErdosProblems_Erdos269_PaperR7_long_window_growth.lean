-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.long_window_growth
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:08:16.751984+00:00
-- url     : https://prove2.me/submissions/2f471e33-3fe1-43e7-b9b4-4070f61f68e9

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_actualWindowBase_eq_product
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_actualWindowProduct_eq_log_monomial
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_actualWindowProduct_geometric_bounds
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























/-- The logarithmic floor used in the paper, with no numerical approximation. -/
theorem natLog_two_pow_eq_floor (b a : ℕ) :
    Nat.log b (2 ^ a) = ⌊(a : ℝ) * Real.logb b 2⌋₊ := by
  rw [← Real.natFloor_logb_natCast b (2 ^ a), Nat.cast_pow, Real.logb_pow]
  norm_num
end ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (lo len : ℕ) (_hlen : 1 ≤ len) :
    actualWindowBase lo len =
      ((2 ^ len *
        3 ^ (⌊((lo + len : ℕ) : ℝ) * Real.logb 3 2⌋₊ -
          ⌊(lo : ℝ) * Real.logb 3 2⌋₊) *
        5 ^ (⌊((lo + len : ℕ) : ℝ) * Real.logb 5 2⌋₊ -
          ⌊(lo : ℝ) * Real.logb 5 2⌋₊) : ℕ) : ℤ) ∧
    (8 : ℝ) ^ len / 15 < (actualWindowBase lo len : ℝ) ∧
    (actualWindowBase lo len : ℝ) < 15 * (8 : ℝ) ^ len := by
  refine ⟨?_, ?_⟩
  · rw [actualWindowBase_eq_product, actualWindowProduct_eq_log_monomial]
    simp only [natLog_two_pow_eq_floor]
    norm_num
  · simpa only [actualWindowBase_eq_product, Int.cast_natCast] using
      actualWindowProduct_geometric_bounds lo len
