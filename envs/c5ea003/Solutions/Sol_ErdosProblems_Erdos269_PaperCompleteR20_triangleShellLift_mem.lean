-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.triangleShellLift_mem
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:22:08.849121+00:00
-- url     : https://prove2.me/submissions/d0b0437d-0d09-44ec-a06f-3457df070d64

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
    (hv : v ∈ literalTriangle a) : triangleShellLift a v ∈ dyadicSmoothShell235 a := by
  have hm : triangleOddPart v ≠ 0 := by simp [triangleOddPart]
  have hk : Nat.log 2 (triangleOddPart v) ≤ a := by
    have := Nat.log_lt_of_lt_pow hm (mem_literalTriangle_iff.mp hv)
    omega
  apply mem_dyadicSmoothShell235_iff.mpr
  change 2 ^ a ≤ 2 ^ (a - Nat.log 2 (triangleOddPart v)) * 3 ^ v.1 * 5 ^ v.2 ∧
    2 ^ (a - Nat.log 2 (triangleOddPart v)) * 3 ^ v.1 * 5 ^ v.2 < 2 ^ (a + 1)
  have he : a - Nat.log 2 (triangleOddPart v) + Nat.log 2 (triangleOddPart v) = a :=
    Nat.sub_add_cancel hk
  constructor
  · have h := Nat.mul_le_mul_left (2 ^ (a - Nat.log 2 (triangleOddPart v)))
      (Nat.pow_log_le_self 2 hm)
    rw [← pow_add, he] at h
    simpa only [triangleOddPart, mul_assoc] using h
  · have h := Nat.mul_lt_mul_of_pos_left
      (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (triangleOddPart v))
      (by positivity : 0 < (2 : ℕ) ^ (a - Nat.log 2 (triangleOddPart v)))
    rw [← pow_add, Nat.succ_eq_add_one, ← Nat.add_assoc, he] at h
    simpa only [triangleOddPart, mul_assoc] using h
