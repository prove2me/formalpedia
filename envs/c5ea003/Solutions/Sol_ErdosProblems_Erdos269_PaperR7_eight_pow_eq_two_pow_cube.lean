-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.eight_pow_eq_two_pow_cube
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:00:45.812086+00:00
-- url     : https://prove2.me/submissions/67e15358-b779-4b7d-8c28-4feabc432aa9

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
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

namespace ErdosProblems.Erdos269.PaperR7
end ErdosProblems.Erdos269.PaperR7

/-!
# Round 7: the literal `8640 / 343` shell bound

Target: the bound in short-note `res:actual-orbit`.  The supplied bound `90`
does not prove this sharper displayed constant.  We retain the actual shell
mass, prove its `8^{-a}` estimate, and sum the resulting majorant exactly.
This is NOT a proof of the separate long-record `Q(n_a)` bound.

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
    (8 : ℕ) ^ a = ((2 : ℕ) ^ a) ^ 3 := by
  calc
    (8 : ℕ) ^ a = ((2 : ℕ) ^ 3) ^ a := by norm_num
    _ = 2 ^ (3 * a) := (pow_mul 2 3 a).symm
    _ = 2 ^ (a * 3) := by rw [Nat.mul_comm 3 a]
    _ = ((2 : ℕ) ^ a) ^ 3 := pow_mul 2 a 3
