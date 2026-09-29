-- Prove2me | Definitions.Def_Bridges_TreeCut_Decomposition
-- name    : Bridges_TreeCut_Decomposition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:02.956644+00:00
-- url     : https://prove2.me/theorems/35a3c7d1-cea2-4891-8dfc-57fe288eaca6
-- title:
--   Aether Catalog definitions — Bridges_TreeCut_Decomposition
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TreeCut.Decomposition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TreeCut/Decomposition.lean by skeleton subtraction
import Mathlib

/-!
# Tree-cut decompositions of finite connected multigraphs

This file formalizes tree-cut decompositions with a strictly layered, non-circular
proof architecture.

* **Layer 1 (definitions + basic facts).** A `Multigraph`, a `TreeCutDecomposition`,
  the two `side`s of a tree edge, the `adhesion` (the set of multigraph edges crossing
  the induced bipartition), the partition property of the bags
  (`TreeCutDecomposition.bag_partition`) and `adhesion_card_eq_cut_size`.
* **Layer 2 (the linked condition).** `TreeCutDecomposition.Linked`, a *pure definition*
  stating that across every tree edge there are `|adhesion|` pairwise edge-disjoint
  paths.  No theorem from Layer 3 is used here.
* **Layer 3 (the main theorem).** `linked_adhesion_eq_minCut`: for a linked
  decomposition the adhesion size of every tree edge equals the edge-min-cut between
  the two sides.  The proof uses only Layers 1 and 2 (it never refers to itself).

The intended imports `Bridges.TreeCut.Sequences` and `Bridges.TreeCut.Multigraph`
are not present in this project, so the multigraph layer is developed locally.

The partition API used is `Setoid.IsPartition` from `Mathlib/Data/Setoid/Partition.lean`
(this Mathlib version has no `Mathlib.Data.Set.Partition`).
-/

universe u w

open scoped Classical

/-- A finite multigraph on a vertex type `V`: a type of `Edge`s together with an
incidence map sending each edge to the unordered pair of its endpoints. -/
structure Multigraph (V : Type u) where
  /-- The edge index type of the multigraph. -/
  Edge : Type u
  /-- Endpoints of each edge, as an unordered pair. -/
  inc : Edge → Sym2 V

namespace Multigraph

variable {V : Type u} (G : Multigraph V)

/-- An edge `e` *crosses* the vertex set `A` if one endpoint lies in `A` and the other
does not. -/
def crosses (A : Set V) (e : G.Edge) : Prop :=
  ∃ x ∈ G.inc e, ∃ y ∈ G.inc e, x ∈ A ∧ y ∉ A

variable {G}

/-
Characterization of crossing in terms of explicit endpoints.
-/

/-
An edge that does not cross `A` keeps both endpoints on the same side.
-/

variable (G)

/-- The set of edges crossing `A`, i.e. the edge cut induced by the bipartition
`(A, Aᶜ)`. -/
noncomputable def cutEdges [Fintype G.Edge] (A : Set V) : Finset G.Edge :=
  Finset.univ.filter (fun e => G.crosses A e)

/-- The size of the cut `(A, Aᶜ)`: the number of multigraph edges between the two
sides. -/
noncomputable def cutSize [Fintype G.Edge] (A : Set V) : ℕ := (G.cutEdges A).card

variable {G}


/-! ### Walks in a multigraph -/

/-- A walk in a multigraph from `a` to `b`: a finite sequence of edges, each connecting
the running vertex to the next. -/
inductive MWalk (G : Multigraph V) : V → V → Type u
  | nil (a : V) : G.MWalk a a
  | cons {a b c : V} (e : G.Edge) (h : G.inc e = s(a, b)) (p : G.MWalk b c) : G.MWalk a c

namespace MWalk

/-- The list of edges traversed by a walk. -/
def edges {G : Multigraph V} : {a b : V} → G.MWalk a b → List G.Edge
  | _, _, .nil _ => []
  | _, _, .cons e _ p => e :: p.edges

end MWalk

/-- An edge set `F` *separates* `A` (from its complement) if there is no walk from a
vertex of `A` to a vertex outside `A` avoiding `F`. -/
def IsSeparator (G : Multigraph V) (A : Set V) (F : Finset G.Edge) : Prop :=
  ∀ u v, u ∈ A → v ∉ A → ¬ ∃ p : G.MWalk u v, ∀ e ∈ p.edges, e ∉ F

/-- The edge min-cut between `A` and its complement: the least size of a separating
edge set. -/
noncomputable def minCut (G : Multigraph V) [Fintype G.Edge] (A : Set V) : ℕ :=
  sInf {n | ∃ F : Finset G.Edge, F.card = n ∧ G.IsSeparator A F}

/-
A walk avoiding `cutEdges A` keeps both endpoints on the same side of `A`.
-/

/-
The cut `cutEdges A` is a separator of `A`.
-/

/-
The set of separator sizes is nonempty (witnessed by `cutEdges A`).
-/

/-
The min-cut is bounded above by the number of edges crossing the bipartition.
-/

/-
There exists an actual separator achieving the min-cut.
-/

/-
Any walk from `A` to its complement must use an edge of every separator.
-/

end Multigraph

/-! ### Tree-cut decompositions (Layer 1) -/

/-- The space of *oriented* tree edges of a tree `T`: ordered adjacent node pairs.
Removing the underlying undirected edge of such an oriented pair splits the tree into
two components; the orientation distinguishes the two sides. -/
def SimpleGraph.AdjSpace {N : Type w} (T : SimpleGraph N) : Type w :=
  {p : N × N // T.Adj p.1 p.2}

/-- A **tree-cut decomposition** of a multigraph `G` over node set `N`:
a decomposition tree `T`, together with pairwise-disjoint, covering, nonempty bags
of vertices indexed by the nodes of `T`. -/
structure TreeCutDecomposition {V : Type u} (G : Multigraph V) (N : Type w) where
  /-- The decomposition tree. -/
  T : SimpleGraph N
  /-- `T` is a tree. -/
  isTree : T.IsTree
  /-- The bag attached to each tree node. -/
  bag : N → Set V
  /-- Every bag is nonempty (needed for the bags to form an honest partition). -/
  bag_nonempty : ∀ n, (bag n).Nonempty
  /-- Distinct nodes carry disjoint bags. -/
  bag_disjoint : ∀ m n, m ≠ n → Disjoint (bag m) (bag n)
  /-- The bags cover all of `V`. -/
  bag_cover : ⋃ n, bag n = Set.univ

namespace TreeCutDecomposition

variable {V : Type u} {G : Multigraph V} {N : Type w}

/-
**Layer 1.** The bags of a tree-cut decomposition form a partition of `V`.
-/

/-- The vertex `side` of an oriented tree edge `e = (x, y)`: the union of the bags of
all nodes reachable from the head `y` once the underlying edge of `e` is deleted from
`T`. -/
def side (D : TreeCutDecomposition G N) (e : D.T.AdjSpace) : Set V :=
  ⋃ (n : N) (_ : (D.T.deleteEdges {s(e.1.1, e.1.2)}).Reachable e.1.2 n), D.bag n

/-- The **adhesion** of an oriented tree edge: the multigraph edges crossing the
bipartition `(side e, (side e)ᶜ)`. -/
noncomputable def adhesion [Fintype G.Edge] (D : TreeCutDecomposition G N)
    (e : D.T.AdjSpace) : Finset G.Edge :=
  G.cutEdges (D.side e)


/-! ### The linked condition (Layer 2) -/

/-- A path crossing the bipartition `(A, Aᶜ)`: a walk whose start lies in `A` and whose
end lies outside `A`. -/
structure CrossPath (G : Multigraph V) (A : Set V) where
  /-- Start vertex of the crossing path. -/
  fst : V
  /-- End vertex of the crossing path. -/
  snd : V
  /-- The underlying walk. -/
  walk : G.MWalk fst snd
  /-- The start is on the `A` side. -/
  fst_mem : fst ∈ A
  /-- The end is on the complementary side. -/
  snd_not_mem : snd ∉ A

/-- The finset of edges used by a crossing path. -/
noncomputable def CrossPath.edgeFinset {G : Multigraph V} {A : Set V}
    (P : CrossPath G A) : Finset G.Edge :=
  P.walk.edges.toFinset

/-- **Layer 2.** A tree-cut decomposition is *linked* if across every tree edge there
are `|adhesion|` pairwise edge-disjoint paths joining the two sides.  This is a pure
definition; it does not refer to the main theorem. -/
def Linked [Fintype G.Edge] (D : TreeCutDecomposition G N) : Prop :=
  ∀ e : D.T.AdjSpace, ∃ P : Fin (D.adhesion e).card → CrossPath G (D.side e),
    ∀ i j, i ≠ j → Disjoint (P i).edgeFinset (P j).edgeFinset

/-! ### The main theorem (Layer 3) -/

/-
Helper for the `≥` direction: if there are `k` pairwise edge-disjoint crossing
paths and `F` is a separator, then `k ≤ |F|`.  Uses only Layers 1–2.
-/

/-
**Layer 3 — main theorem.** For a linked tree-cut decomposition, the adhesion size
of every tree edge equals the edge min-cut between the two sides.

The proof is non-circular: it uses only `cutEdges_isSeparator` /
`minCut_le_cutSize` (Layer 1) and `Linked` together with
`card_le_of_disjoint_crossPaths` (Layer 2).  It never invokes itself.
-/

/-! ### Corollary -/

/-
**Corollary.** Along a ray `e : ℕ → AdjSpace` in the tree, if the adhesions are
nested then their sizes are non-increasing.
-/

end TreeCutDecomposition


