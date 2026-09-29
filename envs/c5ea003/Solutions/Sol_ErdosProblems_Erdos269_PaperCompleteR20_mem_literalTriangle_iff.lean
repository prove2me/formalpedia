-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.mem_literalTriangle_iff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:21:03.77862+00:00
-- url     : https://prove2.me/submissions/d8c320b8-5374-4d7f-b23d-58542e69670e

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangle
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
theorem solution {a : ℕ} {v : ℕ × ℕ} :
    v ∈ literalTriangle a ↔ triangleOddPart v < 2 ^ (a + 1) := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hj : v.1 < a + 1 := by
      by_contra hn
      have h1 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_of_not_gt hn)
      have h2 := Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 3) v.1
      have h3 : 3 ^ v.1 ≤ triangleOddPart v := by
        exact Nat.le_mul_of_pos_right _ (by positivity)
      exact (not_lt_of_ge (h1.trans (h2.trans h3))) h
    have hk : v.2 < a + 1 := by
      by_contra hn
      have h1 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_of_not_gt hn)
      have h2 := Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 5) v.2
      have h3 : 5 ^ v.2 ≤ triangleOddPart v := by
        exact Nat.le_mul_of_pos_left _ (by positivity)
      exact (not_lt_of_ge (h1.trans (h2.trans h3))) h
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hk⟩, h⟩
