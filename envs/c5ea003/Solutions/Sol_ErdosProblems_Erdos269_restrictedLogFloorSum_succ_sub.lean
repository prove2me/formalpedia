-- Prove2me | solution 1 for ErdosProblems.Erdos269.restrictedLogFloorSum_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:17:25.54828+00:00
-- url     : https://prove2.me/submissions/1207aaf5-6729-4f86-b153-48bdd0743c64

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



/-- The admissible two-dimensional exponent pairs are monotone in the
cutoff. -/
theorem strictSmoothPairs_mono
    (q r : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    strictSmoothPairs q r x ⊆ strictSmoothPairs q r y := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨heBox, heVal⟩
  rcases Finset.mem_product.mp heBox with ⟨hj, hk⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, heVal.trans_le hxy⟩
  · exact Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hxy)
  · exact Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hxy)
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (p q r a : ℕ) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    restrictedLogFloorSum p q r (a + 1) -
        restrictedLogFloorSum p q r a =
      (strictSmoothPairs q r (p ^ (a + 1))).card := by
  classical
  let s := strictSmoothPairs q r (p ^ a)
  let t := strictSmoothPairs q r (p ^ (a + 1))
  have hpow : p ^ a ≤ p ^ (a + 1) :=
    Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp) (Nat.le_succ a)
  have hst : s ⊆ t := strictSmoothPairs_mono q r hpow
  have hold : ∀ e ∈ s,
      (a + 1 - Nat.log p (q ^ e.1 * r ^ e.2)) =
        (a - Nat.log p (q ^ e.1 * r ^ e.2)) + 1 := by
    intro e he
    have ht : 0 < q ^ e.1 * r ^ e.2 :=
      Nat.mul_pos (Nat.pow_pos (Nat.zero_lt_of_lt hq))
        (Nat.pow_pos (Nat.zero_lt_of_lt hr))
    have hlt : q ^ e.1 * r ^ e.2 < p ^ a :=
      (Finset.mem_filter.mp he).2
    have hlog : Nat.log p (q ^ e.1 * r ^ e.2) < a :=
      Nat.log_lt_of_lt_pow ht.ne' hlt
    omega
  have hnew : ∀ e ∈ t \ s,
      (a + 1 - Nat.log p (q ^ e.1 * r ^ e.2)) = 1 := by
    intro e he
    have heT := (Finset.mem_sdiff.mp he).1
    have heNotS := (Finset.mem_sdiff.mp he).2
    have hlt : q ^ e.1 * r ^ e.2 < p ^ (a + 1) :=
      (Finset.mem_filter.mp heT).2
    have hle : p ^ a ≤ q ^ e.1 * r ^ e.2 := by
      by_contra h
      apply heNotS
      rcases Finset.mem_filter.mp heT with ⟨heBox, _⟩
      rcases Finset.mem_product.mp heBox with ⟨_hj, _hk⟩
      have hpair : q ^ e.1 * r ^ e.2 < p ^ a := by omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, by omega⟩
      · apply Finset.mem_range.mpr
        exact ((Nat.lt_pow_self hq).trans_le
          (Nat.le_mul_of_pos_right _
            (Nat.pow_pos (Nat.zero_lt_of_lt hr)))).trans hpair
      · apply Finset.mem_range.mpr
        exact ((Nat.lt_pow_self hr).trans_le
          (Nat.le_mul_of_pos_left _
            (Nat.pow_pos (Nat.zero_lt_of_lt hq)))).trans hpair
    have hlog : Nat.log p (q ^ e.1 * r ^ e.2) = a :=
      Nat.log_eq_of_pow_le_of_lt_pow hle hlt
    omega
  have hsucc : restrictedLogFloorSum p q r (a + 1) =
      restrictedLogFloorSum p q r a + t.card := by
    unfold restrictedLogFloorSum
    change (∑ e ∈ t, (a + 1 - Nat.log p (q ^ e.1 * r ^ e.2))) =
      (∑ e ∈ s, (a - Nat.log p (q ^ e.1 * r ^ e.2))) + t.card
    rw [← Finset.sum_sdiff hst]
    rw [Finset.sum_congr rfl hold, Finset.sum_congr rfl hnew]
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_one, Finset.card_sdiff_of_subset hst]
    have hcard : s.card ≤ t.card := Finset.card_le_card hst
    calc
      (t.card - s.card) +
          ((∑ e ∈ s, (a - Nat.log p (q ^ e.1 * r ^ e.2))) + s.card) =
        (∑ e ∈ s, (a - Nat.log p (q ^ e.1 * r ^ e.2))) +
          ((t.card - s.card) + s.card) := by ac_rfl
      _ = (∑ e ∈ s, (a - Nat.log p (q ^ e.1 * r ^ e.2))) + t.card := by
        rw [Nat.sub_add_cancel hcard]
  rw [hsucc]
  exact Nat.add_sub_cancel_left _ _
