-- Prove2me | solution 1 for ErdosProblems.Erdos269.heightNormalizer235_mul_windowMass_eq_int
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:41:21.280986+00:00
-- url     : https://prove2.me/submissions/b92c1f71-be10-4bbf-9e94-dca05801f844

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Theorems.Thm_ErdosProblems_Erdos269_heightNormalizer235_mul_shellMass_eq_nat
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
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (start count : ℕ) :
    ∃ z : ℕ,
      (heightNormalizer235 (start + count) : ℚ) *
        dyadicSmoothWindowMassQ235 start count = (z : ℚ) := by
  classical
  refine ⟨∑ i ∈ Finset.range count,
      ∑ e ∈ dyadicSmoothShell235 (start + i),
        heightNormalizer235 (start + count) /
          threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2), ?_⟩
  rw [dyadicSmoothWindowMassQ235, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hlt : start + i < start + count := by
    have := Finset.mem_range.mp hi
    omega
  exact heightNormalizer235_mul_shellMass_eq_nat hlt
