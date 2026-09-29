-- Prove2me | Theorems.Thm_CollisionFactoring_all_collisions_trivial_of_small
-- name    : CollisionFactoring.all_collisions_trivial_of_small
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:26:16.951612+00:00
-- url     : https://prove2.me/theorems/ad5eb2df-dab1-4c7f-a7ff-66639f82ff4d
-- title:
--   Every collision is trivial when the entries are small.
-- statement:
--   **Every collision is trivial when the entries are small.**  If `r * M < p`
--   then any two `r`-tuples over `A â [1, M]` with congruent sums modulo `p` have
--   *equal* integer sums, so the collision carries no arithmetic information: the
--   gcd step returns `N` or `1`, never a factor.
--
--   ```lean
--   theorem CollisionFactoring.all_collisions_trivial_of_small{p r M : ℕ} {A : Finset ℕ}
--       (hA : ∀ a ∈ A, a ≤ M) (hsmall : r * M < p)
--       {u v : Fin r → ℕ} (hu : u ∈ tupleSpace r A) (hv : v ∈ tupleSpace r A)
--       (hcong : (∑ i, u i) % p = (∑ i, v i) % p) :
--       (∑ i, u i) = ∑ i, v i := by sorry
--   /-! ## End-to-end success -/
--
--
--
--   /-! ## The span barrier: structure never removes it -/
--
--
--
--   /-! ## Both barriers are necessary -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CollisionFactoringSynthesis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CollisionFactoringSynthesis.lean#L84

-- Thm stub generated from Shared/CollisionFactoringSynthesis.lean
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

theorem CollisionFactoring.all_collisions_trivial_of_small{p r M : ℕ} {A : Finset ℕ}
    (hA : ∀ a ∈ A, a ≤ M) (hsmall : r * M < p)
    {u v : Fin r → ℕ} (hu : u ∈ tupleSpace r A) (hv : v ∈ tupleSpace r A)
    (hcong : (∑ i, u i) % p = (∑ i, v i) % p) :
    (∑ i, u i) = ∑ i, v i := by sorry
