-- Prove2me | solution 1 for CollisionFactoring.all_collisions_trivial_of_small
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:08:46.221851+00:00
-- url     : https://prove2.me/submissions/8d3a4588-24cc-4c3a-9ed9-33b779aa69cc

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


theorem mem_sumSet_le {r M : ℕ} {A : Finset ℕ} (hA : ∀ a ∈ A, a ≤ M)
    {s : ℕ} (hs : s ∈ sumSet r A) : s ≤ r * M := by
  simp only [sumSet, Finset.mem_image] at hs
  obtain ⟨u, hu, rfl⟩ := hs
  have hu' : ∀ i : Fin r, u i ∈ A := by
    simpa [tupleSpace, Fintype.mem_piFinset] using hu
  calc ∑ i, u i ≤ ∑ _i : Fin r, M := Finset.sum_le_sum (fun i _ => hA _ (hu' i))
    _ = r * M := by simp



/-! ## End-to-end success -/



/-! ## The span barrier: structure never removes it -/



/-! ## Both barriers are necessary -/




open CollisionFactoring in
theorem solution{p r M : ℕ} {A : Finset ℕ}
    (hA : ∀ a ∈ A, a ≤ M) (hsmall : r * M < p)
    {u v : Fin r → ℕ} (hu : u ∈ tupleSpace r A) (hv : v ∈ tupleSpace r A)
    (hcong : (∑ i, u i) % p = (∑ i, v i) % p) :
    (∑ i, u i) = ∑ i, v i := by
  have hus : (∑ i, u i) ∈ sumSet r A := Finset.mem_image_of_mem _ hu
  have hvs : (∑ i, v i) ∈ sumSet r A := Finset.mem_image_of_mem _ hv
  have h1 := mem_sumSet_le hA hus
  have h2 := mem_sumSet_le hA hvs
  rcases lt_trichotomy (∑ i, u i) (∑ i, v i) with h | h | h
  · exfalso
    have hd : p ∣ (∑ i, v i) - ∑ i, u i := (Nat.modEq_iff_dvd' h.le).mp hcong
    have hpos : 0 < (∑ i, v i) - ∑ i, u i := Nat.sub_pos_of_lt h
    have := Nat.le_of_dvd hpos hd
    omega
  · exact h
  · exfalso
    have hd : p ∣ (∑ i, u i) - ∑ i, v i := (Nat.modEq_iff_dvd' h.le).mp hcong.symm
    have hpos : 0 < (∑ i, u i) - ∑ i, v i := Nat.sub_pos_of_lt h
    have := Nat.le_of_dvd hpos hd
    omega
