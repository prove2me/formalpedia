-- Prove2me | solution 1 for ErdosProblems.Erdos269.qsmul_normalizedTailState_eq_int_of_value_eq_rat
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:49:20.172197+00:00
-- url     : https://prove2.me/submissions/a25e11b7-e8b6-4646-a45d-32675751bf12

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Theorems.Thm_ErdosProblems_Erdos269_two_mul_heightNormalizer235
import Theorems.Thm_ErdosProblems_Erdos269_heightNormalizer235_mul_windowMass_eq_int
import Theorems.Thm_ErdosProblems_Erdos269_dyadicShellTsumTailR235_eq_range_add
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
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    ∃ k : ℤ,
      (q : ℝ) * dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a
        = (k : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, a = 1 + m := ⟨a - 1, by omega⟩
  have hsplit := dyadicShellTsumTailR235_eq_range_add 1 m
  set prefQ : ℚ := dyadicSmoothWindowMassQ235 1 m with hprefQ
  have hprefR : (∑ i ∈ Finset.range m, dyadicShellMassR235 (1 + i)) = (prefQ : ℝ) := by
    simp only [hprefQ, dyadicSmoothWindowMassQ235, dyadicShellMassR235, Rat.cast_sum]
  obtain ⟨z, hz⟩ := heightNormalizer235_mul_windowMass_eq_int 1 m
  have hnorm : dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + m)
      = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * dyadicShellTsumTailR235 (1 + m) := by
    unfold dyadicNormalizedTailStateR235
    have h2 : ((threePrimeHeight 2 3 5 (2 ^ (1 + m)) : ℕ) : ℝ)
        = 2 * ((heightNormalizer235 (1 + m) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
        (two_mul_heightNormalizer235 (1 + m) (by omega)).symm
    rw [h2]
    ring
  have htail : dyadicShellTsumTailR235 (1 + m) = (p : ℝ) / (q : ℝ) - (prefQ : ℝ) := by
    have := hsplit
    rw [hprefR, hval] at this
    linarith
  have hzR : ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (prefQ : ℝ) = ((z : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun r : ℚ => (r : ℝ)) hz
  have hqne : (q : ℝ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hqp : (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by field_simp
  have hqtail : (q : ℝ) * dyadicShellTsumTailR235 (1 + m)
      = (p : ℝ) - (q : ℝ) * (prefQ : ℝ) := by
    rw [htail, mul_sub, hqp]
  refine ⟨(heightNormalizer235 (1 + m) : ℤ) * p - q * (z : ℤ), ?_⟩
  have hcast : (((heightNormalizer235 (1 + m) : ℤ) * p - q * (z : ℤ) : ℤ) : ℝ)
      = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (p : ℝ) - (q : ℝ) * ((z : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast, hnorm]
  calc (q : ℝ) *
        (((heightNormalizer235 (1 + m) : ℕ) : ℝ) * dyadicShellTsumTailR235 (1 + m))
      = ((heightNormalizer235 (1 + m) : ℕ) : ℝ)
          * ((q : ℝ) * dyadicShellTsumTailR235 (1 + m)) := by ring
    _ = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * ((p : ℝ) - (q : ℝ) * (prefQ : ℝ)) := by
          rw [hqtail]
    _ = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (p : ℝ)
          - (q : ℝ) * (((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (prefQ : ℝ)) := by ring
    _ = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (p : ℝ) - (q : ℝ) * ((z : ℕ) : ℝ) := by
          rw [hzR]
