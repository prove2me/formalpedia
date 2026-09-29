-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.actual_numerator_eq_logarithmic_triangle
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:56:23.758329+00:00
-- url     : https://prove2.me/submissions/66a6fdb9-8317-4329-9002-3a9848075248

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_actual_numerator_eq_literal_triangle
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_literalTriangleWeight_eq_logWeight
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
theorem solution (a : ℕ) :
    dyadicOrderedBlockDigit235 a = ∑ v ∈ literalTriangle a, literalLogWeight a v := by
  rw [actual_numerator_eq_literal_triangle]
  exact Finset.sum_congr rfl (fun _ hv => literalTriangleWeight_eq_logWeight hv)
