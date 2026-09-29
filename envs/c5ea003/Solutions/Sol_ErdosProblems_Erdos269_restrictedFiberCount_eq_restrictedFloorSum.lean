-- Prove2me | solution 1 for ErdosProblems.Erdos269.restrictedFiberCount_eq_restrictedFloorSum
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:19:08.204116+00:00
-- url     : https://prove2.me/submissions/ebf08da8-089a-4d14-942f-9a43669e745c

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Theorems.Thm_ErdosProblems_Erdos269_strictSmoothExponent_fiber_card
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
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (p q r x : ℕ) :
    restrictedFiberCount p q r x = restrictedFloorSum p q r x := by
  classical
  unfold restrictedFiberCount restrictedFloorSum
  apply Finset.sum_congr rfl
  intro e he
  exact strictSmoothExponent_fiber_card p q r x he
