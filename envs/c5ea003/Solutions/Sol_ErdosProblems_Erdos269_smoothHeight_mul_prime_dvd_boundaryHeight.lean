-- Prove2me | solution 1 for ErdosProblems.Erdos269.smoothHeight_mul_prime_dvd_boundaryHeight
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:37:02.74569+00:00
-- url     : https://prove2.me/submissions/934f63dc-9197-4415-aed4-0ca45acb9e61

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Theorems.Thm_ErdosProblems_Erdos269_monomial235_dvd
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
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p m x : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5) (hx : 0 < x) (hlt : x < p ^ m) :
    p * threePrimeHeight 2 3 5 x ∣ threePrimeHeight 2 3 5 (p ^ m) := by
  have hxne : x ≠ 0 := hx.ne'
  rcases hp with rfl | rfl | rfl
  · have hlog : Nat.log 2 x < m := Nat.log_lt_of_lt_pow hxne hlt
    have hpow : Nat.log 2 (2 ^ m) = m := Nat.log_pow (by norm_num) m
    have h3 : Nat.log 3 x ≤ Nat.log 3 (2 ^ m) := Nat.log_mono_right hlt.le
    have h5 : Nat.log 5 x ≤ Nat.log 5 (2 ^ m) := Nat.log_mono_right hlt.le
    have hleft : 2 * threePrimeHeight 2 3 5 x
        = 2 ^ (Nat.log 2 x + 1) * 3 ^ Nat.log 3 x * 5 ^ Nat.log 5 x := by
      unfold threePrimeHeight; ring
    have hright : threePrimeHeight 2 3 5 (2 ^ m)
        = 2 ^ m * 3 ^ Nat.log 3 (2 ^ m) * 5 ^ Nat.log 5 (2 ^ m) := by
      unfold threePrimeHeight; rw [hpow]
    rw [hleft, hright]
    exact monomial235_dvd hlog h3 h5
  · have hlog : Nat.log 3 x < m := Nat.log_lt_of_lt_pow hxne hlt
    have hpow : Nat.log 3 (3 ^ m) = m := Nat.log_pow (by norm_num) m
    have h2 : Nat.log 2 x ≤ Nat.log 2 (3 ^ m) := Nat.log_mono_right hlt.le
    have h5 : Nat.log 5 x ≤ Nat.log 5 (3 ^ m) := Nat.log_mono_right hlt.le
    have hleft : 3 * threePrimeHeight 2 3 5 x
        = 2 ^ Nat.log 2 x * 3 ^ (Nat.log 3 x + 1) * 5 ^ Nat.log 5 x := by
      unfold threePrimeHeight; ring
    have hright : threePrimeHeight 2 3 5 (3 ^ m)
        = 2 ^ Nat.log 2 (3 ^ m) * 3 ^ m * 5 ^ Nat.log 5 (3 ^ m) := by
      unfold threePrimeHeight; rw [hpow]
    rw [hleft, hright]
    exact monomial235_dvd h2 hlog h5
  · have hlog : Nat.log 5 x < m := Nat.log_lt_of_lt_pow hxne hlt
    have hpow : Nat.log 5 (5 ^ m) = m := Nat.log_pow (by norm_num) m
    have h2 : Nat.log 2 x ≤ Nat.log 2 (5 ^ m) := Nat.log_mono_right hlt.le
    have h3 : Nat.log 3 x ≤ Nat.log 3 (5 ^ m) := Nat.log_mono_right hlt.le
    have hleft : 5 * threePrimeHeight 2 3 5 x
        = 2 ^ Nat.log 2 x * 3 ^ Nat.log 3 x * 5 ^ (Nat.log 5 x + 1) := by
      unfold threePrimeHeight; ring
    have hright : threePrimeHeight 2 3 5 (5 ^ m)
        = 2 ^ Nat.log 2 (5 ^ m) * 3 ^ Nat.log 3 (5 ^ m) * 5 ^ m := by
      unfold threePrimeHeight; rw [hpow]
    rw [hleft, hright]
    exact monomial235_dvd h2 h3 hlog
