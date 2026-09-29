-- Prove2me | solution 1 for ErdosProblems.Erdos269.threePrimeHeight_smooth_dvd_heightNormalizer235
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:38:35.985469+00:00
-- url     : https://prove2.me/submissions/71a12fe0-6a3d-432c-a861-5d51b2665c8c

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Theorems.Thm_ErdosProblems_Erdos269_smoothHeight_mul_prime_dvd_boundaryHeight
import Theorems.Thm_ErdosProblems_Erdos269_two_mul_heightNormalizer235
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
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {a i j k : ℕ} (hs : smooth3Val 2 3 5 i j k < 2 ^ a) :
    threePrimeHeight 2 3 5 (smooth3Val 2 3 5 i j k) ∣ heightNormalizer235 a := by
  have hsPos : 0 < smooth3Val 2 3 5 i j k := by
    simp only [smooth3Val]
    positivity
  have haPos : 1 ≤ a := by
    by_contra hcon
    have ha0 : a = 0 := by omega
    subst ha0
    rw [pow_zero] at hs
    omega
  have hmul := smoothHeight_mul_prime_dvd_boundaryHeight
    (p := 2) (m := a) (Or.inl rfl) hsPos hs
  rw [← two_mul_heightNormalizer235 a haPos] at hmul
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hmul
