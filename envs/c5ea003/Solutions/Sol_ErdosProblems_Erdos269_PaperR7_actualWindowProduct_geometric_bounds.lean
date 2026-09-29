-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.actualWindowProduct_geometric_bounds
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:06:23.296058+00:00
-- url     : https://prove2.me/submissions/e5d95e3f-0ace-402a-b85d-f9dd4e0289eb

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_eight_pow_lt_fifteen_dyadic_height
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_height_windowProduct
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_actualWindowProduct_pos
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_dyadic_height_le_eight_pow
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
theorem solution (lo len : ℕ) :
    (8 : ℝ) ^ len / 15 < (actualWindowProduct lo len : ℝ) ∧
    (actualWindowProduct lo len : ℝ) < 15 * (8 : ℝ) ^ len := by
  -- Everything is kept at the exponent `lo + len`, and only the very last step
  -- splits `8 ^ (lo + len)`. Rewriting with `pow_add` earlier would also reach
  -- the `2 ^ (lo + len)` sitting inside the height, which must stay folded.
  have hW : (0 : ℝ) < (actualWindowProduct lo len : ℝ) := by
    exact_mod_cast actualWindowProduct_pos lo len
  have hpow : (0 : ℝ) < (8 : ℝ) ^ lo := by positivity
  have hZ : (threePrimeHeight 2 3 5 (2 ^ (lo + len)) : ℝ) =
      (threePrimeHeight 2 3 5 (2 ^ lo) : ℝ) * (actualWindowProduct lo len : ℝ) := by
    exact_mod_cast height_windowProduct lo len
  have hAL : (8 : ℝ) ^ lo < 15 * (threePrimeHeight 2 3 5 (2 ^ lo) : ℝ) :=
    eight_pow_lt_fifteen_dyadic_height lo
  have hAU : (threePrimeHeight 2 3 5 (2 ^ lo) : ℝ) ≤ (8 : ℝ) ^ lo :=
    dyadic_height_le_eight_pow lo
  have hZL : (8 : ℝ) ^ (lo + len) <
      15 * (threePrimeHeight 2 3 5 (2 ^ (lo + len)) : ℝ) :=
    eight_pow_lt_fifteen_dyadic_height (lo + len)
  have hZU : (threePrimeHeight 2 3 5 (2 ^ (lo + len)) : ℝ) ≤ (8 : ℝ) ^ (lo + len) :=
    dyadic_height_le_eight_pow (lo + len)
  have h8 : (8 : ℝ) ^ (lo + len) = (8 : ℝ) ^ lo * (8 : ℝ) ^ len := pow_add 8 lo len
  rw [hZ, h8] at hZL hZU
  constructor
  · apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 15)).mpr
    have hmul : (8 : ℝ) ^ lo * (8 : ℝ) ^ len <
        (8 : ℝ) ^ lo * ((actualWindowProduct lo len : ℝ) * 15) := by
      nlinarith [mul_le_mul_of_nonneg_right hAU hW.le]
    exact lt_of_mul_lt_mul_left hmul hpow.le
  · have hmul : (8 : ℝ) ^ lo * (actualWindowProduct lo len : ℝ) <
        (8 : ℝ) ^ lo * (15 * (8 : ℝ) ^ len) := by
      nlinarith [mul_lt_mul_of_pos_right hAL hW]
    exact lt_of_mul_lt_mul_left hmul hpow.le
