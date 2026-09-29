-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.literalTriangleWeight_four_values
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:42:12.206846+00:00
-- url     : https://prove2.me/submissions/d31827e8-c1cd-445d-8aa1-e4f20dcc6451

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangle
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_triangleShellLift_mem
import Theorems.Thm_ErdosProblems_Erdos269_oddHeightSuffix235_eq_thresholdFactors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
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

/-!
# The actual shell numerator as a finite weighted triangle

The map below identifies each odd exponent pair with its unique binary
multiple in the dyadic shell. All inequalities are exact integer inequalities.
The logarithmic coordinates and asymptotic bounds are separate consumers.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open scoped BigOperators
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution {a : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ literalTriangle a) :
    literalTriangleWeight a v = 1 ∨ literalTriangleWeight a v = 3 ∨
      literalTriangleWeight a v = 5 ∨ literalTriangleWeight a v = 15 := by
  unfold literalTriangleWeight
  rw [oddHeightSuffix235_eq_thresholdFactors (triangleShellLift_mem hv)]
  split_ifs <;> norm_num
