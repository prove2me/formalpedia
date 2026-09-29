-- Prove2me | solution 1 for ErdosProblems.Erdos269.strictPExponentFiber_card_at_pow
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:19:08.753599+00:00
-- url     : https://prove2.me/submissions/e9a46fb8-163c-42a7-88de-ee352a8e04a8

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
    (p q r a : ℕ) {e : ℕ × ℕ}
    (hp : 1 < p) (hq : 0 < q) (hr : 0 < r)
    (he : e ∈ strictSmoothPairs q r (p ^ a)) :
    (strictPExponentFiber p q r (p ^ a) e).card =
      a - Nat.log p (q ^ e.1 * r ^ e.2) := by
  classical
  let t := q ^ e.1 * r ^ e.2
  have ht : 0 < t := by
    dsimp [t]
    exact Nat.mul_pos (Nat.pow_pos hq) (Nat.pow_pos hr)
  have htCut : t < p ^ a := (Finset.mem_filter.mp he).2
  have hset : strictPExponentFiber p q r (p ^ a) e =
      Finset.range (a - Nat.log p t) := by
    ext i
    simp only [strictPExponentFiber, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_hiRange, hiVal⟩
      have hpowLog : p ^ Nat.log p t ≤ t := Nat.pow_log_le_self p ht.ne'
      have hpowBound : p ^ (i + Nat.log p t) < p ^ a := by
        rw [pow_add]
        exact (Nat.mul_le_mul_left (p ^ i) hpowLog).trans_lt hiVal
      have hiLog : i + Nat.log p t < a :=
        (Nat.pow_lt_pow_iff_right hp).mp hpowBound
      omega
    · intro hi
      have hiA : i < a := by omega
      refine ⟨hiA.trans (Nat.lt_pow_self hp), ?_⟩
      have htUpper : t < p ^ (Nat.log p t + 1) :=
        Nat.lt_pow_succ_log_self hp t
      calc
        p ^ i * (q ^ e.1 * r ^ e.2) = p ^ i * t := by rfl
        _ < p ^ i * p ^ (Nat.log p t + 1) :=
          (Nat.mul_lt_mul_left (Nat.pow_pos (Nat.zero_lt_of_lt hp))).mpr htUpper
        _ = p ^ (i + (Nat.log p t + 1)) :=
          (pow_add p i (Nat.log p t + 1)).symm
        _ ≤ p ^ a := Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp) (by omega)
  rw [hset, Finset.card_range]
