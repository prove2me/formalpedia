-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.shell_projection_injective
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:21:43.147978+00:00
-- url     : https://prove2.me/submissions/87b32a26-2f3b-49ea-80e4-a28657e620a3

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangle
import Theorems.Thm_ErdosProblems_Erdos269_exponent_unique_in_short_interval
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
theorem solution {a : ℕ} {e f : ℕ × ℕ × ℕ}
    (he : e ∈ dyadicSmoothShell235 a) (hf : f ∈ dyadicSmoothShell235 a)
    (h : e.2 = f.2) : e = f := by
  rcases e with ⟨i, v⟩
  rcases f with ⟨j, w⟩
  change v = w at h
  subst w
  have hi := mem_dyadicSmoothShell235_iff.mp he
  have hj := mem_dyadicSmoothShell235_iff.mp hf
  have hij : i = j := exponent_unique_in_short_interval
    (base := 2) (lo := 2 ^ a) (hi := 2 ^ (a + 1)) (weight := triangleOddPart v)
    (by norm_num) (by rw [pow_succ]; omega)
    (by simpa [smooth3Val, triangleOddPart, mul_assoc] using hi.1)
    (by simpa [smooth3Val, triangleOddPart, mul_assoc] using hi.2)
    (by simpa [smooth3Val, triangleOddPart, mul_assoc] using hj.1)
    (by simpa [smooth3Val, triangleOddPart, mul_assoc] using hj.2)
  subst j
  rfl
