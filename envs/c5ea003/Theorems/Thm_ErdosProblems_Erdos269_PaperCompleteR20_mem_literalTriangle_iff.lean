-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_mem_literalTriangle_iff
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.mem_literalTriangle_iff
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:20:54.406932+00:00
-- url     : https://prove2.me/theorems/6e61bd80-1769-4b71-a807-8c6ffdfc04ec
-- title:
--   Mem literalTriangle iff
-- statement:
--   A pair of odd exponents lies in the literal triangle exactly when its 3^j5^k odd part is below 2^(a+1).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/LiteralTriangle.lean#L21-L42
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

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


open scoped BigOperators

open ErdosProblems.Erdos269.PaperCompleteR20

theorem ErdosProblems.Erdos269.PaperCompleteR20.mem_literalTriangle_iff {a : ℕ} {v : ℕ × ℕ} :
    v ∈ literalTriangle a ↔ triangleOddPart v < 2 ^ (a + 1) := by sorry
