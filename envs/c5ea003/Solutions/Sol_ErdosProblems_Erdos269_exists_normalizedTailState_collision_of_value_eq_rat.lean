-- Prove2me | solution 1 for ErdosProblems.Erdos269.exists_normalizedTailState_collision_of_value_eq_rat
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:50:18.77071+00:00
-- url     : https://prove2.me/submissions/53deb98f-f5d5-4454-8476-78e7f5f31cb3

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Theorems.Thm_ErdosProblems_Erdos269_exists_int_sub_of_qsmul_int
import Theorems.Thm_ErdosProblems_Erdos269_qsmul_normalizedTailState_eq_int_of_value_eq_rat
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
# Erdős #269: rationality forces an all-scale lattice, and the collision target

Let `S = ∑_{smooth s ≥ 2} 1/H(s)` with `H` the running `{2,3,5}` LCM height, and
let `X_a = (H(2^a)/2) · T_a` be the normalized dyadic tail state.

Three things are proved here.

1.  **Clearing at every prime-power boundary.**  For `p ∈ {2,3,5}`, `m ≥ 1` and
    every smooth `x < p^m`, one has `p · H(x) ∣ H(p^m)`.  The dyadic case
    `p = 2` is the clearing used by the tail recurrence; the `p = 3` and
    `p = 5` cases are new and give two further families of boundaries at which
    the same rational prefix clears.

2.  **All-scale rationality lattice.**  If `S = p/q` then *every* `X_a` lies on
    the `(1/q)`-lattice simultaneously, with an explicit integer witness.  This
    is the arithmetic reduction, no irrationality claim.

3.  **The collision target.**  Rationality does not merely produce one
    exceptional integral state: by pigeonhole on `(1/q)ℤ / ℤ` it forces two
    distinct scales whose tail states differ by an *integer*.  Contrapositive:
    if the normalized tail states are pairwise incongruent mod `1`, then `S` is
    irrational.  The `q = 1` "integral state" branch is the special case
    `X_a - 0 ∈ ℤ`; the collision statement covers every denominator at once.

Nothing here claims irrationality.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators

/-! ### Monomial clearing -/





/-! ### The dyadic half-height normalizer -/







/-! ### Clearing the rational prefix -/









/-! ### The all-scale lattice -/



/-! ### The collision target -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ i j : ℕ, i < j ∧ ∃ z : ℤ,
      dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + j) -
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + i) = (z : ℝ) :=
  exists_int_sub_of_qsmul_int hq
    (fun n => dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + n))
    (fun n => qsmul_normalizedTailState_eq_int_of_value_eq_rat hq hval (by omega))
