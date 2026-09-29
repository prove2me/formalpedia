-- Prove2me | Theorems.Thm_D10_markOn_eq_of_equivariant_equiv
-- name    : D10.markOn_eq_of_equivariant_equiv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:27:14.423872+00:00
-- url     : https://prove2.me/theorems/a90fc3a6-9103-4516-96ac-0a82c584f83a
-- title:
--   Marks are invariants of the isomorphism type of a `G`-set.
-- statement:
--   Marks are invariants of the isomorphism type of a `G`-set.
--
--   ```lean
--   theorem D10.markOn_eq_of_equivariant_equiv(e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
--       (H : Subgroup G) [Fintype H] : markOn X H = markOn Y H := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/MolienBurnsideD10.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/MolienBurnsideD10.lean#L249

-- Thm stub generated from NumberTheory/MolienBurnsideD10.lean
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

theorem D10.markOn_eq_of_equivariant_equiv(e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
    (H : Subgroup G) [Fintype H] : markOn X H = markOn Y H := by sorry
