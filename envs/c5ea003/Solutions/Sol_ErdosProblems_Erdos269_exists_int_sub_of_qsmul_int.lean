-- Prove2me | solution 1 for ErdosProblems.Erdos269.exists_int_sub_of_qsmul_int
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:47:04.36123+00:00
-- url     : https://prove2.me/submissions/3bbe18fa-2ae0-4dff-8009-a5cc6398ae87

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
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
theorem solution {q : ℤ} (hq : 0 < q) (x : ℕ → ℝ)
    (h : ∀ n : ℕ, ∃ k : ℤ, (q : ℝ) * x n = (k : ℝ)) :
    ∃ i j : ℕ, i < j ∧ ∃ z : ℤ, x j - x i = (z : ℝ) := by
  classical
  choose k hk using h
  set Q : ℕ := q.toNat with hQ
  have hQpos : 0 < Q := by omega
  have hQcast : ((Q : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq.le
  haveI : NeZero Q := ⟨hQpos.ne'⟩
  have hcard : (Finset.univ : Finset (ZMod Q)).card < (Finset.range (Q + 1)).card := by
    simpa [Finset.card_univ, ZMod.card] using Nat.lt_succ_self Q
  obtain ⟨i, -, j, -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (f := fun n : ℕ => ((k n : ℤ) : ZMod Q)) hcard (fun n _ => Finset.mem_univ _)
  have hdvd : ∀ u v : ℕ,
      ((k u : ℤ) : ZMod Q) = ((k v : ℤ) : ZMod Q) → (q : ℤ) ∣ k v - k u := by
    intro u v huv
    have hzero : (((k v - k u : ℤ)) : ZMod Q) = 0 := by
      push_cast
      rw [huv]
      ring
    have hd : ((Q : ℕ) : ℤ) ∣ (k v - k u) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
    rwa [hQcast] at hd
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have main : ∀ u v : ℕ, (q : ℤ) ∣ k v - k u → ∃ z : ℤ, x v - x u = (z : ℝ) := by
    intro u v hd
    obtain ⟨z, hz⟩ := hd
    refine ⟨z, ?_⟩
    have hmul : (q : ℝ) * (x v - x u) = (q : ℝ) * (z : ℝ) := by
      rw [mul_sub, hk v, hk u, ← Int.cast_sub, hz]
      push_cast
      ring
    exact mul_left_cancel₀ hqne hmul
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨i, j, hlt, main i j (hdvd i j heq)⟩
  · exact ⟨j, i, hlt, main j i (hdvd j i heq.symm)⟩
