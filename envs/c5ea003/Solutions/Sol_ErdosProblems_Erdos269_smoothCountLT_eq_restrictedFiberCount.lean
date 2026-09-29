-- Prove2me | solution 1 for ErdosProblems.Erdos269.smoothCountLT_eq_restrictedFiberCount
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:21:15.158836+00:00
-- url     : https://prove2.me/submissions/b0759bea-3b4e-41c5-aa3d-a1b28c0cb225

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

















/-! ## Exact two-dimensional fiber formula -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (p q r x : ℕ) (hp : 0 < p) :
    smoothCountLT p q r x = restrictedFiberCount p q r x := by
  classical
  unfold smoothCountLT restrictedFiberCount
  apply Finset.card_eq_sum_card_fiberwise
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hbox, hval⟩
  rcases Finset.mem_product.mp hbox with ⟨_hi, hjk⟩
  rcases Finset.mem_product.mp hjk with ⟨hj, hk⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hj, hk⟩, ?_⟩
  have hval' : p ^ z.1 * (q ^ z.2.1 * r ^ z.2.2) < x := by
    simpa [smooth3Val, mul_assoc] using hval
  exact
    (Nat.le_mul_of_pos_left (q ^ z.2.1 * r ^ z.2.2)
      (Nat.pow_pos hp : 0 < p ^ z.1)).trans_lt hval'
