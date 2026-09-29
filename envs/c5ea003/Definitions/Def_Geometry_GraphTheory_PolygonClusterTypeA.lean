-- Prove2me | Definitions.Def_Geometry_GraphTheory_PolygonClusterTypeA
-- name    : Geometry_GraphTheory_PolygonClusterTypeA
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:17:05.199765+00:00
-- url     : https://prove2.me/theorems/dcc9f334-5ef7-481b-a00e-6be54230f637
-- title:
--   Aether Catalog definitions — Geometry_GraphTheory_PolygonClusterTypeA
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.GraphTheory.PolygonClusterTypeA`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/GraphTheory/PolygonClusterTypeA.lean by skeleton subtraction
import Mathlib
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

namespace PolygonClusterTypeA

/-! ## 1. Diagonals of a convex `m`-gon

We label the vertices of a convex `m`-gon by `Fin m`, arranged cyclically.  The cyclic
successor of vertex `i` is `nextV i`.  A **side** is an (unordered) pair `{i, i+1}` of
cyclically adjacent vertices; a **diagonal** is an unordered pair of distinct, non-adjacent
vertices.  Everything is counted as an honest `Finset`. -/

/-- The cyclic successor of a polygon vertex. -/
def nextV {m : ℕ} (i : Fin m) : Fin m :=
  ⟨(i.1 + 1) % m, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩


/-- `e` is a **side** of the `m`-gon: an edge joining two cyclically adjacent vertices. -/
def IsSide (m : ℕ) (e : Sym2 (Fin m)) : Prop := ∃ i : Fin m, e = s(i, nextV i)

instance (m : ℕ) (e : Sym2 (Fin m)) : Decidable (IsSide m e) := by
  unfold IsSide; infer_instance



/-- The set of diagonals of the convex `m`-gon: unordered pairs of distinct, non-adjacent
vertices. -/
def diagonalFinset (m : ℕ) : Finset (Sym2 (Fin m)) :=
  Finset.univ.filter (fun e => ¬ e.IsDiag ∧ ¬ IsSide m e)

/-- The number of diagonals of a convex `m`-gon. -/
def diagonalCount (m : ℕ) : ℕ := (diagonalFinset m).card





/-! ## 2. Triangulations as binary trees (clusters of type `A`)

By the dual-tree bijection, a triangulation of a convex `m`-gon is the same datum as a
binary tree with `m - 2` internal nodes (`Tree Unit` with `numNodes = m - 2`).  We take
this as the definition of a triangulation / cluster.  The rank parameter is `r = m - 3`
(type `A_r` ↔ `m = r + 3`). -/

/-- A **triangulation** (= cluster) of a convex `m`-gon, modelled by its dual binary tree:
a `Tree Unit` with `m - 2` internal nodes (one per triangle). -/
def Triangulation (m : ℕ) : Type := {t : Tree Unit // t.numNodes = m - 2}

/-- The explicit finite enumeration of all triangulations of an `m`-gon, i.e. of all
clusters of the type `A_{m-3}` cluster algebra. -/
def clusters (m : ℕ) : Finset (Tree Unit) := treesOfNumNodesEq (m - 2)

/-- The set of triangulations is finite, witnessed by the *genuine enumeration*
`treesOfNumNodesEq (m - 2)` (not by abstract type-class search). -/
instance Triangulation.fintype (m : ℕ) : Fintype (Triangulation m) :=
  Fintype.subtype (treesOfNumNodesEq (m - 2)) (fun _ => mem_treesOfNumNodesEq)

/-- The number of diagonals of a triangulation: the number of internal edges of its dual
tree, i.e. `numNodes - 1`. -/
def numDiagonals {m : ℕ} (t : Triangulation m) : ℕ := t.val.numNodes - 1






/-! ## 3. Flips and the exchange graph

A **flip** of a triangulation removes one diagonal and replaces it by the other diagonal
of the resulting quadrilateral.  Under the dual-tree bijection a flip is exactly a single
**rotation** of the binary tree, the classical edges of the associahedron.  We define the
rotation relation inductively and take the symmetric, irreflexive version as the adjacency
of the exchange graph. -/

/-- A single binary-tree **rotation** somewhere inside the tree.  The base case
`node (node a b) c ↝ node a (node b c)` is one flip of a diagonal; the two recursive cases
allow rotating inside a subtree. -/
inductive Rotation : Tree Unit → Tree Unit → Prop where
  | root (a b c : Tree Unit) :
      Rotation (.node () (.node () a b) c) (.node () a (.node () b c))
  | left {a a' b : Tree Unit} : Rotation a a' → Rotation (.node () a b) (.node () a' b)
  | right {a b b' : Tree Unit} : Rotation b b' → Rotation (.node () a b) (.node () a b')






/-! ## 4. Examples / sanity checks (small `m`)

These small finite checks may use `native_decide`; the general theorems above do not. -/

end PolygonClusterTypeA


