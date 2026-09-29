-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.actual_numerator_eq_literal_triangle
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:46:14.884632+00:00
-- url     : https://prove2.me/submissions/198cad4a-8efd-4b3c-a039-414bef3c8b86

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangle
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_mem_literalTriangle_iff
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_shell_projection_injective
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_triangleShellLift_mem
import Theorems.Thm_ErdosProblems_Erdos269_dyadicHalfClearedMass235_eq_orderedBlockDigit235
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











theorem shell_projection_mem_triangle {a : ℕ} {e : ℕ × ℕ × ℕ}
    (he : e ∈ dyadicSmoothShell235 a) : e.2 ∈ literalTriangle a := by
  apply mem_literalTriangle_iff.mpr
  have hs := (mem_dyadicSmoothShell235_iff.mp he).2
  have hle : triangleOddPart e.2 ≤ smooth3Val 2 3 5 e.1 e.2.1 e.2.2 := by
    simpa only [triangleOddPart, smooth3Val, mul_assoc] using
      (Nat.le_mul_of_pos_left (triangleOddPart e.2) (by positivity : 0 < (2 : ℕ) ^ e.1))
  exact hle.trans_lt hs



theorem triangleShellLift_projection {a : ℕ} {e : ℕ × ℕ × ℕ}
    (he : e ∈ dyadicSmoothShell235 a) : triangleShellLift a e.2 = e :=
  shell_projection_injective (triangleShellLift_mem (shell_projection_mem_triangle he)) he rfl
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution (a : ℕ) :
    dyadicOrderedBlockDigit235 a =
      ∑ v ∈ literalTriangle a, literalTriangleWeight a v := by
  rw [← dyadicHalfClearedMass235_eq_orderedBlockDigit235]
  unfold dyadicHalfClearedMass235
  refine Finset.sum_bij (fun e _ => e.2)
    (fun _ he => shell_projection_mem_triangle he)
    (fun _ he _ hf h => shell_projection_injective he hf h) ?_ ?_
  · intro v hv
    exact ⟨triangleShellLift a v, triangleShellLift_mem hv, rfl⟩
  · intro e he
    simp only [literalTriangleWeight, triangleShellLift_projection he]
