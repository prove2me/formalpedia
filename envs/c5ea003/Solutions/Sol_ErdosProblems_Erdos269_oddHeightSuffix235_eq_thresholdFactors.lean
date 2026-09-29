-- Prove2me | solution 1 for ErdosProblems.Erdos269.oddHeightSuffix235_eq_thresholdFactors
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:23:49.864988+00:00
-- url     : https://prove2.me/submissions/790a8f07-4345-48e4-be0e-c8eff851872b

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Theorems.Thm_ErdosProblems_Erdos269_pow_log_dyadic_suffix_eq_if
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
# Erdős #269: all-scale internal-threshold partition

The preceding block-mass module proves that every cleared dyadic-shell term is
`2` times an odd suffix product.  Here that suffix is identified pointwise and
then summed: the only tests are whether the smooth point lies before the unique
internal `3`-power and `5`-power thresholds.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {a : ℕ} {e : ℕ × ℕ × ℕ} (he : e ∈ dyadicSmoothShell235 a) :
    oddHeightSuffix235 a e =
      (if smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
          3 ^ Nat.log 3 (2 ^ (a + 1)) then 3 else 1) *
      (if smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
          5 ^ Nat.log 5 (2 ^ (a + 1)) then 5 else 1) := by
  have hshell := mem_dyadicSmoothShell235_iff.mp he
  have hx : 0 < smooth3Val 2 3 5 e.1 e.2.1 e.2.2 := by
    simp [smooth3Val]
  unfold oddHeightSuffix235
  rw [pow_log_dyadic_suffix_eq_if (by norm_num : 2 ≤ 3) hx hshell.1 hshell.2,
    pow_log_dyadic_suffix_eq_if (by norm_num : 2 ≤ 5) hx hshell.1 hshell.2]
