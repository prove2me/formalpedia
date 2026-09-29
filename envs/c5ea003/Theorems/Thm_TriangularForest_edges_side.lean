-- Prove2me | Theorems.Thm_TriangularForest_edges_side
-- name    : TriangularForest.edges_side
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:24:20.085959+00:00
-- url     : https://prove2.me/theorems/ff7308f3-60e1-4fc1-afa0-a1d819ae9854
-- title:
--   Along a walk none of whose non-final vertices is the gluing vertex `x`, all edges lie on the
-- statement:
--   Along a walk none of whose non-final vertices is the gluing vertex `x`, all edges lie on the
--   same side of the 1-sum.
--
--   ```lean
--   theorem TriangularForest.edges_side(hx : ∀ y : V, (∃ u, G₁.Adj y u) → (∃ w, G₂.Adj y w) → y = x)
--       {u w : V} (p : (G₁ ⊔ G₂).Walk u w) (hne : ∀ i < p.length, p.getVert i ≠ x) :
--       (∀ e ∈ p.edges, e ∈ G₁.edgeSet) ∨ (∀ e ∈ p.edges, e ∈ G₂.edgeSet) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TriangularForest/OneSum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TriangularForest/OneSum.lean#L24

-- Thm stub generated from Logic/TriangularForest/OneSum.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_ClassProperties

/-!
# Triangular forests are closed under 1-sums

A *1-sum* of two graphs glues them along a single vertex.  Together with closure under
subgraphs, decidable membership, containing a triangle and not being everything, this is one of
the properties the Lee–Liu–Tsai framework requires of the graph class `F`.

The formalisation keeps both summands on the same vertex type: `G₁` and `G₂` are graphs whose
supports meet in at most one vertex `x`, and the 1-sum is `G₁ ⊔ G₂`.

The combinatorial core is `TriangularForest.edges_side`: along a walk that avoids `x` at every
position except possibly its last, consecutive edges are forced to stay on the same side, since
a vertex incident to an edge of `G₁` and to an edge of `G₂` must be the gluing vertex `x`.  A
cycle can then be transferred wholesale into `G₁` or into `G₂`, where it is a triangle.
-/

open TriangularForest

-- open removed: section is not a namespace

variable {V : Type*} {G₁ G₂ : SimpleGraph V} {x : V}

theorem TriangularForest.edges_side(hx : ∀ y : V, (∃ u, G₁.Adj y u) → (∃ w, G₂.Adj y w) → y = x)
    {u w : V} (p : (G₁ ⊔ G₂).Walk u w) (hne : ∀ i < p.length, p.getVert i ≠ x) :
    (∀ e ∈ p.edges, e ∈ G₁.edgeSet) ∨ (∀ e ∈ p.edges, e ∈ G₂.edgeSet) := by sorry
