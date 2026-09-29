-- Prove2me | solution 1 for ErdosProblems.Erdos269.strictSmoothExponents_mono
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:16:35.116916+00:00
-- url     : https://prove2.me/submissions/ee206369-2835-4223-bb74-103660607e0d

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
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
    strictSmoothExponents p q r x ⊆ strictSmoothExponents p q r y := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨hbox, hval⟩
  rcases Finset.mem_product.mp hbox with ⟨hi, hjk⟩
  rcases Finset.mem_product.mp hjk with ⟨hj, hk⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hxy), ?_⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hxy),
      Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hxy)⟩
  · exact hval.trans_le hxy
