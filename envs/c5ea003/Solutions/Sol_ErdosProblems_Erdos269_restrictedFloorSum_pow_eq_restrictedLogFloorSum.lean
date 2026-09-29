-- Prove2me | solution 1 for ErdosProblems.Erdos269.restrictedFloorSum_pow_eq_restrictedLogFloorSum
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:21:14.683855+00:00
-- url     : https://prove2.me/submissions/96e1267d-c648-4288-8aa2-b123051b3a81

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Theorems.Thm_ErdosProblems_Erdos269_strictPExponentFiber_card_at_pow
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
    (p q r a : ℕ) (hp : 1 < p) (hq : 0 < q) (hr : 0 < r) :
    restrictedFloorSum p q r (p ^ a) = restrictedLogFloorSum p q r a := by
  classical
  unfold restrictedFloorSum restrictedLogFloorSum
  apply Finset.sum_congr rfl
  intro e he
  exact strictPExponentFiber_card_at_pow p q r a hp hq hr he
