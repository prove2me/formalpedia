-- Prove2me | solution 1 for ErdosProblems.Erdos269.smooth3Val_dvd_threePrimeHeight_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:28:02.506291+00:00
-- url     : https://prove2.me/submissions/d9a553b6-53ba-4f48-a290-6e5d36f243f7

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the three-prime running-LCM coordinate

This module starts the problem-owned formalization of the first unresolved
three-prime case.  It records the exact computational height used by the
running-LCM representation, its cubic majorant, the smallest non-separation
fixture for `{2,3,5}`, the variable-base tail-state update, and the uniform
quadratic bound for actual filtered smooth-number shells.

No declaration here asserts irrationality or transcendence of a three-prime
value.  The missing producer is still an infinite residue-escape or genuinely
higher-dimensional analytic theorem.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p q r x : ℕ} {e : ℕ × ℕ × ℕ}
    (he : e ∈ smoothPrefixExponents p q r x) :
    smooth3Val p q r e.1 e.2.1 e.2.2 ∣ threePrimeHeight p q r x := by
  have hbox := (Finset.mem_filter.mp he).1
  have hpBox := Finset.mem_product.mp hbox
  have hqrBox := Finset.mem_product.mp hpBox.2
  have hpExp : e.1 ≤ Nat.log p x := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hpBox.1)
  have hqExp : e.2.1 ≤ Nat.log q x := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hqrBox.1)
  have hrExp : e.2.2 ≤ Nat.log r x := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hqrBox.2)
  exact mul_dvd_mul
    (mul_dvd_mul (pow_dvd_pow p hpExp) (pow_dvd_pow q hqExp))
    (pow_dvd_pow r hrExp)
