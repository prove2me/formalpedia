-- Prove2me | solution 1 for ErdosProblems.Erdos269.restrictedPurePowerCount_eq_restrictedLogFloorSum
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:22:26.8584+00:00
-- url     : https://prove2.me/submissions/462491d1-e08b-4744-92a9-7d451a52cb92

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Theorems.Thm_ErdosProblems_Erdos269_restrictedFiberCount_eq_restrictedFloorSum
import Theorems.Thm_ErdosProblems_Erdos269_restrictedFloorSum_pow_eq_restrictedLogFloorSum
import Theorems.Thm_ErdosProblems_Erdos269_smoothCountLT_eq_restrictedFiberCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
# Erdős #269: restricted floor sums and local windows

Problem-owned landing surface for the exact true-shell floor sums and the
local-window residue reduction.  No declaration here asserts the open
cofinal anti-concentration theorem.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators

/-! ## Exact finite strict counts -/

















/-! ## Exact two-dimensional fiber formula -/

























/-- Exact restricted two-dimensional floor-sum formula for the strict
three-prime smooth count. -/
theorem smoothCountLT_eq_restrictedFloorSum
    (p q r x : ℕ) (hp : 0 < p) :
    smoothCountLT p q r x = restrictedFloorSum p q r x := by
  rw [smoothCountLT_eq_restrictedFiberCount p q r x hp,
    restrictedFiberCount_eq_restrictedFloorSum]



/-- At a pure `p`-power cutoff, the exact count is the literal restricted
two-dimensional floor sum. -/
theorem restrictedPurePowerCount_eq_restrictedFloorSum
    (p q r a : ℕ) (hp : 0 < p) :
    restrictedPurePowerCount p q r a = restrictedFloorSum p q r (p ^ a) := by
  exact smoothCountLT_eq_restrictedFloorSum p q r (p ^ a) hp
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (p q r a : ℕ) (hp : 1 < p) (hq : 0 < q) (hr : 0 < r) :
    restrictedPurePowerCount p q r a = restrictedLogFloorSum p q r a := by
  rw [restrictedPurePowerCount_eq_restrictedFloorSum p q r a
      (Nat.zero_lt_of_lt hp),
    restrictedFloorSum_pow_eq_restrictedLogFloorSum p q r a hp hq hr]
