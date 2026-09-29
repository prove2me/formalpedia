-- Prove2me | Definitions.Def_Shared_CollisionFactoringSynthesis
-- name    : Shared_CollisionFactoringSynthesis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:49:48.251652+00:00
-- url     : https://prove2.me/theorems/6f39129e-1998-479a-b917-90337cdd7a61
-- title:
--   Aether Catalog definitions — Shared_CollisionFactoringSynthesis
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CollisionFactoringSynthesis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CollisionFactoringSynthesis.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_BirthdayBoundHierarchy
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

namespace CollisionFactoring

open Finset ThreeSumReveal BirthdayHierarchy

/-! ## Nontrivial collisions come from a large *sumset* -/


/-! ## The set of sums of `r`-tuples -/

/-- All integer sums achieved by `r`-tuples over `A`. -/
noncomputable def sumSet (r : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (tupleSpace r A).image (fun u => ∑ i, u i)




/-! ## End-to-end success -/



/-! ## The span barrier: structure never removes it -/



/-! ## Both barriers are necessary -/



end CollisionFactoring


