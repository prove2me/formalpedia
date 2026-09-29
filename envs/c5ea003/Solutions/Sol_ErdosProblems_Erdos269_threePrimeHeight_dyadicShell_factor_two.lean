-- Prove2me | solution 1 for ErdosProblems.Erdos269.threePrimeHeight_dyadicShell_factor_two
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:12:22.22809+00:00
-- url     : https://prove2.me/submissions/d1ff95bb-2917-4ceb-82cf-2190a4ec01c8

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
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
# Erdős #269: exact dyadic block-mass normalization

The integer checker compresses the smooth numbers in a half-open dyadic shell
`[2^a, 2^(a+1))`.  After clearing by the height at the right endpoint, every
summand contains the terminal dyadic factor `2`.  Dividing that common factor
leaves a suffix product of the zero, one, or two internal odd-prime jumps.

This file kernel-checks the complete cell algebra used by the checker.  The
remaining source-specific step is to identify the cell cardinalities with the
appropriate `strictSmoothShell` filters for every `a`.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators







/-- Every point of the half-open dyadic shell has binary logarithmic
coordinate exactly `a`.  This is the all-scale source fact behind the common
terminal factor `2` in the cleared block mass. -/
theorem log_two_eq_of_mem_dyadicSmoothShell235
    {a : ℕ} {e : ℕ × ℕ × ℕ} (he : e ∈ dyadicSmoothShell235 a) :
    Nat.log 2 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) = a := by
  exact Nat.log_eq_of_pow_le_of_lt_pow
    (mem_dyadicSmoothShell235_iff.mp he).1
    (mem_dyadicSmoothShell235_iff.mp he).2
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {a : ℕ} {e : ℕ × ℕ × ℕ} (he : e ∈ dyadicSmoothShell235 a) :
    threePrimeHeight 2 3 5 (2 ^ (a + 1)) =
      2 * oddHeightSuffix235 a e *
        threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) := by
  let x := smooth3Val 2 3 5 e.1 e.2.1 e.2.2
  have hxUpper : x ≤ 2 ^ (a + 1) := by
    exact (mem_dyadicSmoothShell235_iff.mp he).2.le
  have hlog2 : Nat.log 2 x = a := by
    exact log_two_eq_of_mem_dyadicSmoothShell235 he
  have h3le : Nat.log 3 x ≤ Nat.log 3 (2 ^ (a + 1)) :=
    Nat.log_mono_right hxUpper
  have h5le : Nat.log 5 x ≤ Nat.log 5 (2 ^ (a + 1)) :=
    Nat.log_mono_right hxUpper
  have h3pow :
      3 ^ Nat.log 3 (2 ^ (a + 1)) =
        3 ^ (Nat.log 3 (2 ^ (a + 1)) - Nat.log 3 x) * 3 ^ Nat.log 3 x := by
    rw [← pow_add, Nat.sub_add_cancel h3le]
  have h5pow :
      5 ^ Nat.log 5 (2 ^ (a + 1)) =
        5 ^ (Nat.log 5 (2 ^ (a + 1)) - Nat.log 5 x) * 5 ^ Nat.log 5 x := by
    rw [← pow_add, Nat.sub_add_cancel h5le]
  simp only [threePrimeHeight, oddHeightSuffix235]
  change
    2 ^ Nat.log 2 (2 ^ (a + 1)) *
          3 ^ Nat.log 3 (2 ^ (a + 1)) * 5 ^ Nat.log 5 (2 ^ (a + 1)) =
      2 *
          (3 ^ (Nat.log 3 (2 ^ (a + 1)) - Nat.log 3 x) *
            5 ^ (Nat.log 5 (2 ^ (a + 1)) - Nat.log 5 x)) *
        (2 ^ Nat.log 2 x * 3 ^ Nat.log 3 x * 5 ^ Nat.log 5 x)
  rw [Nat.log_pow (by norm_num : 1 < 2), hlog2, h3pow, h5pow, pow_succ]
  ring
