-- Prove2me | solution 1 for RainbowForestDeletion.deletion_objective_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:39:34.055283+00:00
-- url     : https://prove2.me/submissions/4dcb75f3-0da7-4fd8-b226-1ce9aa3912cf

-- Sol generated from Novelty/RainbowForestDeletion.lean
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






/-!
### Non-vacuity: an honest obstruction

We exhibit concrete monotone rank functions and a target `t` for which the Rainbow Forest
Inequality genuinely fails, so the obstruction hypotheses above are inhabited and none of
the theorems is vacuously true.  On the two-edge ground set `Bool`, both matroids are free
(`r A = |A|`), so `obj(A) = |A| + |Aᶜ| = 2` for every `A`; with `t = 3` the inequality fails
everywhere while, by `no_edge_minimal_obstruction`, no deletion can repair it.
-/





open RainbowForestDeletion in
theorem solution{r₁ r₂ : Finset α → ℤ}
    (h1 : Monotone r₁) (h2 : Monotone r₂) (e : α) (A : Finset α) :
    r₁ (A.erase e) + r₂ ((univ.erase e) \ (A.erase e)) ≤ obj r₁ r₂ A := by
  -- first term: `A.erase e ⊆ A`
  have ht1 : r₁ (A.erase e) ≤ r₁ A := h1 (Finset.erase_subset e A)
  -- second term: `(E \ {e}) \ (A.erase e) ⊆ Aᶜ`
  have hsub : (univ.erase e) \ (A.erase e) ⊆ Aᶜ := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_erase] at hx
    rw [Finset.mem_compl]
    obtain ⟨⟨hxe, _⟩, hxA⟩ := hx
    intro hxinA
    exact hxA (Finset.mem_erase.mpr ⟨hxe, hxinA⟩)
  have ht2 : r₂ ((univ.erase e) \ (A.erase e)) ≤ r₂ Aᶜ := h2 hsub
  have : r₁ (A.erase e) + r₂ ((univ.erase e) \ (A.erase e)) ≤ r₁ A + r₂ Aᶜ := by linarith
  simpa [obj] using this
