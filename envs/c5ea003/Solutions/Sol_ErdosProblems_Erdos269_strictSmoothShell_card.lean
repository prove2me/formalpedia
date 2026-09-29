-- Prove2me | solution 1 for ErdosProblems.Erdos269.strictSmoothShell_card
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:17:38.585643+00:00
-- url     : https://prove2.me/submissions/0eed3af1-0ac0-41d5-9733-cdc50305a2a8

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Theorems.Thm_ErdosProblems_Erdos269_strictSmoothExponents_mono
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
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (p q r : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    (strictSmoothShell p q r x y).card =
      smoothCountLT p q r y - smoothCountLT p q r x := by
  exact Finset.card_sdiff_of_subset (strictSmoothExponents_mono p q r hxy)
