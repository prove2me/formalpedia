-- Prove2me | solution 1 for ErdosProblems.Erdos269.smoothCountLT_swap_first_second
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:21:31.478623+00:00
-- url     : https://prove2.me/submissions/a8d070b1-0d7b-4e3f-8446-e3dc2a45dfd6

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
theorem solution (p q r x : ℕ) :
    smoothCountLT p q r x = smoothCountLT q p r x := by
  classical
  unfold smoothCountLT
  apply Finset.card_bij (fun z _hz => (z.2.1, z.1, z.2.2))
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzBox, hzVal⟩
    rcases Finset.mem_product.mp hzBox with ⟨hi, hjk⟩
    rcases Finset.mem_product.mp hjk with ⟨hj, hk⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨hj, Finset.mem_product.mpr ⟨hi, hk⟩⟩, ?_⟩
    simpa [smooth3Val, mul_assoc, mul_left_comm, mul_comm] using hzVal
  · intro z₁ _hz₁ z₂ _hz₂ hEq
    rcases z₁ with ⟨i₁, j₁, k₁⟩
    rcases z₂ with ⟨i₂, j₂, k₂⟩
    injection hEq with hj hrest
    injection hrest with hi hk
    simp only at hi hj hk
    exact Prod.ext hi (Prod.ext hj hk)
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzBox, hzVal⟩
    rcases Finset.mem_product.mp hzBox with ⟨hj, hik⟩
    rcases Finset.mem_product.mp hik with ⟨hi, hk⟩
    refine ⟨(z.2.1, z.1, z.2.2), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨hi, Finset.mem_product.mpr ⟨hj, hk⟩⟩, ?_⟩
      simpa [smooth3Val, mul_assoc, mul_left_comm, mul_comm] using hzVal
    · rcases z with ⟨j, i, k⟩
      rfl
