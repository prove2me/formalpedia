-- Prove2me | solution 1 for ErdosProblems.Erdos269.strictSmoothExponent_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:17:26.332756+00:00
-- url     : https://prove2.me/submissions/972bd076-ccf3-41ef-a31f-1b936f5ce5b6

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
    (p q r x : ℕ) {e : ℕ × ℕ} (he : e ∈ strictSmoothPairs q r x) :
    ((strictSmoothExponents p q r x).filter
      fun z => (z.2.1, z.2.2) = e).card =
      (strictPExponentFiber p q r x e).card := by
  classical
  apply Finset.card_bij (fun z _hz => z.1)
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzSmooth, hzProj⟩
    rcases Finset.mem_filter.mp hzSmooth with ⟨hzBox, hzVal⟩
    rcases Finset.mem_product.mp hzBox with ⟨hi, _hjk⟩
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    have hj : z.2.1 = e.1 := congrArg Prod.fst hzProj
    have hk : z.2.2 = e.2 := congrArg Prod.snd hzProj
    rw [← hj, ← hk]
    simpa [smooth3Val, mul_assoc] using hzVal
  · intro z₁ hz₁ z₂ hz₂ hfirst
    have hproj₁ := (Finset.mem_filter.mp hz₁).2
    have hproj₂ := (Finset.mem_filter.mp hz₂).2
    apply Prod.ext hfirst
    apply Prod.ext
    · exact (congrArg Prod.fst hproj₁).trans (congrArg Prod.fst hproj₂).symm
    · exact (congrArg Prod.snd hproj₁).trans (congrArg Prod.snd hproj₂).symm
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hiRange, hiVal⟩
    rcases Finset.mem_filter.mp he with ⟨heBox, _heVal⟩
    rcases Finset.mem_product.mp heBox with ⟨hj, hk⟩
    refine ⟨(i, e.1, e.2), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hiRange, Finset.mem_product.mpr ⟨hj, hk⟩⟩, ?_⟩, rfl⟩
    simpa [smooth3Val, mul_assoc] using hiVal
