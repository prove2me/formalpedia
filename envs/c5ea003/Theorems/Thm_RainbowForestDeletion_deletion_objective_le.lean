-- Prove2me | Theorems.Thm_RainbowForestDeletion_deletion_objective_le
-- name    : RainbowForestDeletion.deletion_objective_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:27:10.832269+00:00
-- url     : https://prove2.me/theorems/c74212e1-dc1d-4b10-8630-04bf25a530b3
-- title:
--   The Edmonds objective can only drop under deletion.
-- statement:
--   **The Edmonds objective can only drop under deletion.**  For every subset `A`, using the
--   deleted subset `A.erase e ⊆ E \ {e}`, the objective of `G - e` is at most the objective of
--   `G`:
--   `r₁(A.erase e) + r₂((E \ {e}) \ (A.erase e)) ≤ obj_G(A)`.
--   Hence a subset witnessing an obstruction in `G` still witnesses one after deleting any edge.
--
--   ```lean
--   theorem RainbowForestDeletion.deletion_objective_le{r₁ r₂ : Finset α → ℤ}
--       (h1 : Monotone r₁) (h2 : Monotone r₂) (e : α) (A : Finset α) :
--       r₁ (A.erase e) + r₂ ((univ.erase e) \ (A.erase e)) ≤ obj r₁ r₂ A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/RainbowForestDeletion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/RainbowForestDeletion.lean#L133

-- Thm stub generated from Novelty/RainbowForestDeletion.lean
import Mathlib
import Definitions.Def_Novelty_RainbowForestDeletion
/-
# Minimal obstructions to total rainbow forests: the edge-deletion analysis

## Setting

Fix a finite ground set `α`, thought of as the edge set `E(G)` of an edge-coloured graph.
Two matroids live on this ground set:

* the **cycle (graphic) matroid** `M₁`, whose independent sets are the forests of `G`,
  with rank function `r₁`;
* the **partition matroid** `M₂` induced by the colouring, whose independent sets are the
  *rainbow* edge sets (at most one edge of each colour), with rank function `r₂`.

A **total rainbow forest** is a set of edges that is simultaneously a forest and rainbow,
i.e. a common independent set of `M₁` and `M₂`.  Write

  `obj(A) = r₁(A) + r₂(Aᶜ)`   (the Edmonds intersection objective, `Aᶜ = E \ A`).

By **Edmonds' Matroid Intersection Theorem** the maximum size of a total rainbow forest
equals `min_{A ⊆ E} obj(A)`.  The **Rainbow Forest Inequality (RFI)** at target `t` is the
assertion that `t ≤ obj(A)` for every `A ⊆ E`; equivalently a total rainbow forest of size
`t` exists.

## What this file proves

The mission conjecture reads: *for a minimal obstruction to total rainbow forests there is a
unique subset `A` with `obj(A) < t`, and the failure is strict for no other subset.*  We
analyse this through the natural notion of **minimality under edge deletion**: `G` is an
edge-minimal obstruction if RFI fails for `G` but holds for every single-edge deletion
`G - e`.

The central discovery is that this notion is **vacuous for matroids**:

1. `rainbow_forest_inequality` — the easy (weak-duality) direction of Edmonds' theorem:
   every common independent set `I` satisfies `|I| ≤ obj(A)` for all `A`.  Hence the
   existence of a size-`t` total rainbow forest forces RFI (`RFI_of_commonIndep`).
2. `deletion_objective_le` — the Edmonds objective of the deletion `G - e` never exceeds the
   objective of `G`: for every `A`, `obj_{G-e}(A.erase e) ≤ obj_G(A)`.  Thus **RFI-failure
   is closed under edge deletion**.
3. `deletionRFI_imp_RFI` — if even a *single* deletion `G - e` satisfies RFI, then `G`
   already satisfies RFI.
4. `no_edge_minimal_obstruction` — consequently there is **no edge-minimal obstruction**:
   the hypotheses "RFI fails for `G`" and "RFI holds for every `G - e`" are contradictory
   for genuine (monotone) matroid ranks.

This is a *root-cause* explanation of why the uniqueness reading of the mission fails: one
cannot even speak of a well-defined edge-minimal obstruction, because the certifying subset
of an obstruction survives every deletion (`deletion_preserves_obstruction`).

The final section exhibits an honest, non-vacuous obstruction, so none of the statements
above are vacuously true.
-/


open Finset

open RainbowForestDeletion

variable {α : Type*} [Fintype α] [DecidableEq α]



/-!
### The Rainbow Forest Inequality via weak duality

A **common independent set** of the two matroids is a set all of whose subsets have full
rank in both matroids (downward-closed independence).  This is exactly a total rainbow
forest together with its hereditary independence.
-/




/-!
### Edge deletion and the collapse of "minimal obstruction"

Deleting an edge `e` produces the matroids `M₁ \ e`, `M₂ \ e` on the ground set `E \ {e}`.
Restriction rank equals the ambient rank on subsets of `E \ {e}`, so the objective of the
deletion at a subset `A ⊆ E \ {e}` is `r₁(A) + r₂((E \ {e}) \ A)`.
-/

theorem RainbowForestDeletion.deletion_objective_le{r₁ r₂ : Finset α → ℤ}
    (h1 : Monotone r₁) (h2 : Monotone r₂) (e : α) (A : Finset α) :
    r₁ (A.erase e) + r₂ ((univ.erase e) \ (A.erase e)) ≤ obj r₁ r₂ A := by sorry
