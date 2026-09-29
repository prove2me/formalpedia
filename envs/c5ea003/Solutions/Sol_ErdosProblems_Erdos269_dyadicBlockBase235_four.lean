-- Prove2me | solution 1 for ErdosProblems.Erdos269.dyadicBlockBase235_four
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:01:36.710746+00:00
-- url     : https://prove2.me/submissions/2c658653-278f-40df-a86a-b3e66abf4d64

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight_dyadicBlock_succ
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































/-! ## Finite pure-power jump enumeration -/

















/-! ## Single-coordinate jump ratios -/













/-! ## Finite jump grouping -/













/-! The first exact `{2,3,5}` kernel values. -/















/-! ## Exact short-shell multiplicity bounds -/













/-! ## Exact dyadic block geometry for `{2,3,5}` -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
@[simp] theorem solution : dyadicBlockBase235 4 = 30 := by
  have h := threePrimeHeight_dyadicBlock_succ 4
  have h2sixteen : Nat.log 2 16 = 4 := by
    simpa using Nat.log_pow (b := 2) (by norm_num : 1 < 2) 4
  have h3sixteen : Nat.log 3 16 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h5sixteen : Nat.log 5 16 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h2thirtytwo : Nat.log 2 32 = 5 := by
    simpa using Nat.log_pow (b := 2) (by norm_num : 1 < 2) 5
  have h3thirtytwo : Nat.log 3 32 = 3 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h5thirtytwo : Nat.log 5 32 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  norm_num [threePrimeHeight, h2sixteen, h3sixteen, h5sixteen,
    h2thirtytwo, h3thirtytwo, h5thirtytwo] at h ⊢
  omega
