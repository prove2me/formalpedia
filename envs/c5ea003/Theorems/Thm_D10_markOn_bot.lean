-- Prove2me | Theorems.Thm_D10_markOn_bot
-- name    : D10.markOn_bot
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:25:57.908465+00:00
-- url     : https://prove2.me/theorems/81b9309a-d2a9-4f31-9c9d-e50ac541347a
-- title:
--   MarkOn bot
-- statement:
--   Formal statement of `D10.markOn_bot` from the Aether Catalog (NumberTheory). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem D10.markOn_bot: markOn X (⊥ : Subgroup G) = Fintype.card X := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/MolienBurnsideD10.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/MolienBurnsideD10.lean#L74

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

theorem D10.markOn_bot: markOn X (⊥ : Subgroup G) = Fintype.card X := by sorry
