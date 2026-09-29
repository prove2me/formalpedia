-- Prove2me | solution 1 for CollisionFactoring.span_barrier
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:08:46.727096+00:00
-- url     : https://prove2.me/submissions/46d2b33e-8751-45ba-8c74-13a9c37ce96a

-- Sol generated from Shared/CollisionFactoringSynthesis.lean
import Mathlib
import Definitions.Def_Shared_BirthdayBoundHierarchy
import Definitions.Def_Shared_CollisionFactoringSynthesis
import Definitions.Def_Shared_ThreeSumFactorReveal

/-!
# End-to-end collision factoring, and the two barriers it must pass

This file glues the two halves of the story together:

* the *reveal* lemma of `Catalog.Shared.ThreeSumFactorReveal`
  (a congruence mod `p` below `N` produces `p` by one gcd), and
* the *birthday bound* of `Catalog.Shared.BirthdayBoundHierarchy`
  (a collision is guaranteed exactly when the search space exceeds `p`),

and it isolates a second, independent obstruction that the naive "cost = number
of tuples" accounting hides.

**Barrier 1 (counting).**  A guaranteed `r`-SUM collision needs more than `p`
tuples, hence more than `√N` work at any arity `r`.

**Barrier 2 (amplitude).**  A collision is *useful* only if the two colliding
tuples have different integer sums.  All `r`-tuples drawn from `A ⊆ [1, M]` have
sums in `[r, rM]`, so at most `rM - r + 1` distinct sums exist.  If `r * M < p`
then *every* modular collision is trivial (`all_collisions_trivial_of_small`)
and the scheme cannot factor at all, no matter how many tuples are inspected.
Thus the entries themselves must be of size `≥ p / r`, and the useful search
space is capped by `r * M`, not by `|A| ^ r`.

The master theorem `rsum_factoring_success` shows that once both barriers are
passed the scheme provably outputs the factor `p`.

Main results:

* `useful_collision_of_sumset_card_lt` — a sumset larger than `p` contains a
  nontrivial modular collision.
* `rsum_factoring_success` — end-to-end: it outputs `gcd = p`.
* `all_collisions_trivial_of_small` — the amplitude barrier.
* `sumset_card_le_amplitude` — the useful search space is at most `r * M`.
* `rsum_needs_both_barriers` — a successful scheme must satisfy `p ≤ r * M`
  *and* inspect more than `√N` tuples.
-/

open CollisionFactoring

open Finset ThreeSumReveal BirthdayHierarchy

/-! ## Nontrivial collisions come from a large *sumset* -/


/-! ## The set of sums of `r`-tuples -/





/-! ## End-to-end success -/



/-! ## The span barrier: structure never removes it -/



/-! ## Both barriers are necessary -/




open CollisionFactoring in
theorem solution{p L : ℕ} {T : Finset ℕ}
    (hT : ∀ x ∈ T, L ≤ x ∧ x < L + p) :
    ∀ s ∈ T, ∀ t ∈ T, s % p = t % p → s = t := by
  intro s hs t ht hst
  obtain ⟨hs1, hs2⟩ := hT s hs
  obtain ⟨ht1, ht2⟩ := hT t ht
  rcases lt_trichotomy s t with h | h | h
  · have hd : p ∣ t - s := (Nat.modEq_iff_dvd' h.le).mp hst
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt h) hd
    omega
  · exact h
  · have hd : p ∣ s - t := (Nat.modEq_iff_dvd' h.le).mp hst.symm
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt h) hd
    omega
