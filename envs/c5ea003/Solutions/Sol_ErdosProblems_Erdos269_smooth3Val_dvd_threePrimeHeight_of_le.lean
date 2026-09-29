-- Prove2me | solution 1 for ErdosProblems.Erdos269.smooth3Val_dvd_threePrimeHeight_of_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:08:50.161102+00:00
-- url     : https://prove2.me/submissions/434e646e-b145-4ce1-8cc8-abbae70521c8

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







































/-! ## Generic logarithmic-window algebra -/



















/-! ## Exact denominator-factor cancellation -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p q r i j k x : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hcut : smooth3Val p q r i j k ≤ x) :
    smooth3Val p q r i j k ∣ threePrimeHeight p q r x := by
  have hpPow : p ^ i ≤ smooth3Val p q r i j k := by
    unfold smooth3Val
    exact (Nat.le_mul_of_pos_right _
      (Nat.pow_pos (Nat.zero_lt_of_lt hq))).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.zero_lt_of_lt hr)))
  have hqPow : q ^ j ≤ smooth3Val p q r i j k := by
    unfold smooth3Val
    exact (Nat.le_mul_of_pos_left _
      (Nat.pow_pos (Nat.zero_lt_of_lt hp))).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.zero_lt_of_lt hr)))
  have hrPow : r ^ k ≤ smooth3Val p q r i j k := by
    unfold smooth3Val
    exact Nat.le_mul_of_pos_left _
      (Nat.mul_pos (Nat.pow_pos (Nat.zero_lt_of_lt hp))
        (Nat.pow_pos (Nat.zero_lt_of_lt hq)))
  have hi : i ≤ Nat.log p x :=
    Nat.le_log_of_pow_le hp (hpPow.trans hcut)
  have hj : j ≤ Nat.log q x :=
    Nat.le_log_of_pow_le hq (hqPow.trans hcut)
  have hk : k ≤ Nat.log r x :=
    Nat.le_log_of_pow_le hr (hrPow.trans hcut)
  exact mul_dvd_mul (mul_dvd_mul (pow_dvd_pow p hi) (pow_dvd_pow q hj))
    (pow_dvd_pow r hk)
