-- Prove2me | Theorems.Thm_PolygonClusterTypeA_diagonalCount_eq
-- name    : PolygonClusterTypeA.diagonalCount_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:35:55.160877+00:00
-- url     : https://prove2.me/theorems/65e8ceef-5fd0-4fea-b464-7bd0c363d85b
-- title:
--   The number of diagonals equals (all unordered pairs of distinct vertices) minus
-- statement:
--   The number of diagonals equals (all unordered pairs of distinct vertices) minus
--   (the sides): `m choose 2 - m`.
--
--   ```lean
--   theorem PolygonClusterTypeA.diagonalCount_eq(m : ℕ) (hm : 3 ≤ m) : diagonalCount m = m.choose 2 - m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/GraphTheory/PolygonClusterTypeA.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/GraphTheory/PolygonClusterTypeA.lean#L128

-- Thm stub generated from Geometry/GraphTheory/PolygonClusterTypeA.lean
import Mathlib
import Definitions.Def_Geometry_GraphTheory_PolygonClusterTypeA
/-
# The polygon / associahedron model of the finite type `A` cluster algebra of `Gr(2, m)`

This file gives a **self-contained, fully proved** combinatorial model of the finite
type `A` cluster complex, the cluster structure that governs the Grassmannian `Gr(2, m)`
of 2-planes in `m`-space.

## The `Gr(2, m)` / polygon dictionary

The homogeneous coordinate ring of `Gr(2, m)` (in its Plücker embedding) is a cluster
algebra of finite type `A_{m-3}`.  Its combinatorics is encoded by a **convex `m`-gon**:

* Plücker coordinates `p_{ij}` (`1 ≤ i < j ≤ m`)  ↔  segments between vertices `i`, `j`.
* the `m` *frozen* coordinates `p_{i,i+1}`        ↔  the `m` **sides** of the polygon.
* the `m(m-3)/2` *mutable* coordinates            ↔  the **diagonals** of the polygon.
* clusters (maximal collections of compatible mutable variables)
                                                  ↔  **triangulations** of the polygon.
* mutations of clusters                           ↔  **flips** of triangulations.

Type `A_r` corresponds to a convex polygon with `r + 3` vertices; each of its clusters
has exactly `r` mutable variables (diagonals).  Equivalently, for an `m`-gon the rank is
`r = m - 3`.

## What is formalized here

We use the classical bijection between triangulations of a convex `m`-gon and binary
trees with `m - 2` internal nodes (the dual tree of a triangulation): a triangulation of
an `m`-gon has `m - 2` triangles and `m - 3` diagonals, and the dual graph that joins two
triangles sharing a diagonal is a tree with `m - 2` nodes and `m - 3` edges.  Under this
dictionary

* triangles            ↔ internal nodes of the binary tree,
* diagonals            ↔ internal edges of the binary tree (`numNodes - 1` of them),
* flips of a diagonal  ↔ rotations of the binary tree.

The number of such trees is the Catalan number `catalan (m - 2)`, recovering the count of
triangulations / clusters.

Main results:

* `two_mul_diagonalCount` — a convex `m`-gon (`m ≥ 3`) has `m(m-3)/2` diagonals, in the
  division-free form `2 * diagonalCount m = m * (m - 3)`.  This is proved from a genuine
  enumeration of the diagonals as a `Finset` of `Sym2 (Fin m)`.
* `rank_constant` — every triangulation of an `m`-gon has exactly `m - 3` diagonals.
* `Triangulation.fintype` + `card_triangulation` — there are finitely many clusters,
  and exactly `catalan (m - 2)` of them (Catalan enumeration), built from the genuine
  enumeration `treesOfNumNodesEq`.
* `card_clusters_typeA` — type `A_r` has `catalan (r + 1)` clusters.
* `exchangeGraph` + `exchangeGraph_finite` — the flip / exchange graph has finitely many
  vertices.

## Relation to the Schubert-cell conjecture

This file does **not** prove the general statement that every Schubert cell in a type `A`
flag variety carries a cluster structure of a prescribed type.  It formalizes only the
single, completely understood case `Gr(2, m)` (the "big cell" / open Schubert cell of the
Grassmannian), whose cluster type is the finite type `A_{m-3}` realized by the polygon /
associahedron above.  See `FUTURE_DIRECTIONS.md` for the bridge back to the general
problem.
-/

open Tree

open PolygonClusterTypeA

/-! ## 1. Diagonals of a convex `m`-gon

We label the vertices of a convex `m`-gon by `Fin m`, arranged cyclically.  The cyclic
successor of vertex `i` is `nextV i`.  A **side** is an (unordered) pair `{i, i+1}` of
cyclically adjacent vertices; a **diagonal** is an unordered pair of distinct, non-adjacent
vertices.  Everything is counted as an honest `Finset`. -/

theorem PolygonClusterTypeA.diagonalCount_eq(m : ℕ) (hm : 3 ≤ m) : diagonalCount m = m.choose 2 - m := by sorry
