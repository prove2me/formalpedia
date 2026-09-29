-- Prove2me | solution 1 for D10.card_group_dvd_sum_fixCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:02:21.432866+00:00
-- url     : https://prove2.me/submissions/a0450a50-65d9-4916-8ee2-27044adfed3b

-- Sol generated from NumberTheory/MolienBurnsideD10.lean
import Mathlib
import Definitions.Def_NumberTheory_MolienBurnsideD10

/-!
# Conjecture D10: is the Molien invariant exactly the Burnside mark vector modulo scaling?

For a finite group `G` acting on a finite set `X` there are two classical invariants.

* the **Burnside mark vector** `H ↦ markOn X H = |X^H|`, indexed by the subgroups of `G`;
* the **Molien invariant** `H ↦ molien X H = (1/|H|) ∑_{h ∈ H} |X^h|`, the subgroup-wise
  average of the permutation character (equivalently, by Burnside's lemma, the number of
  `H`-orbits, equivalently the constant term data of the Molien series of the permutation
  representation restricted to `H`).

Conjecture D10 asserts that these two invariants agree up to a scalar.  This file settles
the conjecture:

* **positive half** (`molien_eq_avgMarks`): the Molien invariant is always a *linear image*
  of the mark vector — it is the average over `h ∈ H` of the marks at the cyclic subgroups
  `⟨h⟩`.  Hence the mark vector determines the Molien invariant.
* **sharp positive result** (`markOn_eq_of_fixCount_eq_of_cyclic`): if every subgroup of `G`
  is cyclic (e.g. `G` cyclic), the Molien invariant conversely determines the whole mark
  vector *on the nose* (scaling factor `1`).
* **negative half** (`D10_false`): for the Klein four group `V = (ℤ/2)²` there are two
  `V`-sets with *identical* Molien invariants at every subgroup whose mark vectors are not
  proportional.  So Conjecture D10 is **false** in general, and the cyclic hypothesis above
  is exactly the boundary of its validity.

Along the way we prove the structural comparison `markOn ≤ molien` with the equality case
(`molien_eq_markOn_iff`), Burnside's orbit-counting identity in this normalisation
(`molien_eq_card_orbits`) and the resulting arithmetic divisibility
`|H| ∣ ∑_{h ∈ H} |X^h|`.
-/

open D10

open Finset MulAction


variable {G : Type*} [Group G]






variable {G : Type*} [Group G] {X : Type*} [MulAction G X] [Fintype X] [DecidableEq X]









variable {G : Type*} [Group G] {X : Type*} [MulAction G X] [Fintype X] [DecidableEq X]














variable {G : Type*} [Group G] {X Y : Type*}
  [MulAction G X] [Fintype X] [DecidableEq X] [MulAction G Y] [Fintype Y] [DecidableEq Y]







/-! ### The Klein four group counterexample

Let `V = ℤ/2 × ℤ/2` (written multiplicatively).  Its three subgroups of index two are the
kernels of the three surjections `χ₀(a,b) = a`, `χ₁(a,b) = b`, `χ₂(a,b) = a + b`.

* `Xthree` is the disjoint union `V/A ⊔ V/B ⊔ V/C` of the three transitive two-element
  `V`-sets;
* `Xreg` is the disjoint union of the regular `V`-set with two fixed points.

Both have six elements and, as we verify, *identical permutation characters*; hence
identical Molien invariants at every subgroup.  Their mark vectors, however, disagree at
the top subgroup (`0` versus `2`), and no rescaling can repair this. -/
























open D10 in
theorem solution[Fintype G] :
    Fintype.card G ∣ ∑ g : G, fixCount X g := by
  classical
  refine ⟨Nat.card (Quotient (MulAction.orbitRel G X)), ?_⟩
  have key := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (α := G) (β := X)
  rw [Nat.card_eq_fintype_card, mul_comm, ← key]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fintype.card_eq_nat_card, Nat.card_eq_card_toFinset, fixCount]
  congr 1
  ext x
  simp only [MulAction.fixedBy, Set.mem_setOf_eq, Set.mem_toFinset, mem_filter, mem_univ, true_and]
