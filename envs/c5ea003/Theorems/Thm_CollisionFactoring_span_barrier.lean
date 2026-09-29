-- Prove2me | Theorems.Thm_CollisionFactoring_span_barrier
-- name    : CollisionFactoring.span_barrier
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:26:20.100245+00:00
-- url     : https://prove2.me/theorems/774c5e42-5488-4fef-8c0b-be1e1b5d7b9b
-- title:
--   Span barrier (arity- and structure-free).
-- statement:
--   **Span barrier (arity- and structure-free).**  If every value produced by a
--   scheme lies in an interval of length `p` (i.e. `L â¤ x < L + p`), then congruent
--   values are equal: no useful collision exists.  This holds for *any* collision
--   scheme â sumset, 3SUM, `r`-SUM, or an evaluation scheme such as singular moduli
--   â because it constrains only the numerical values, not how they are produced.
--   Consequently the values themselves must span a range of size at least `p`, and
--   for `q â¤ p` at least `âN`.
--
--   ```lean
--   theorem CollisionFactoring.span_barrier{p L : ℕ} {T : Finset ℕ}
--       (hT : ∀ x ∈ T, L ≤ x ∧ x < L + p) :
--       ∀ s ∈ T, ∀ t ∈ T, s % p = t % p → s = t := by sorry
--
--   /-! ## Both barriers are necessary -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CollisionFactoringSynthesis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CollisionFactoringSynthesis.lean#L139

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





/-! ## End-to-end success -/



/-! ## The span barrier: structure never removes it -/

theorem CollisionFactoring.span_barrier{p L : ℕ} {T : Finset ℕ}
    (hT : ∀ x ∈ T, L ≤ x ∧ x < L + p) :
    ∀ s ∈ T, ∀ t ∈ T, s % p = t % p → s = t := by sorry
