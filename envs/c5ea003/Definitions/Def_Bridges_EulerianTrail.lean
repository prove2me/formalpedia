-- Prove2me | Definitions.Def_Bridges_EulerianTrail
-- name    : Bridges_EulerianTrail
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:52.601907+00:00
-- url     : https://prove2.me/theorems/e00fc46d-ace3-4847-b74e-8e29b62e9fff
-- title:
--   Aether Catalog definitions — Bridges_EulerianTrail
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.EulerianTrail`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/EulerianTrail.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_GraphTheory_Multigraph
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Eulerian Trails and the Parity Theorem

We define Eulerian trails in finite multigraphs and prove the fundamental
**Euler Parity Theorem**: a multigraph admitting an Eulerian trail has at
most two vertices of odd degree.

## Main Definitions

* `Bridges.EulerianTrail` : An Eulerian trail in a multigraph.
* `Bridges.EulerianTrail.visitCount` : Number of times a vertex appears in the vertex sequence.

## Main Results

* `Bridges.EulerianTrail.degree_visit_identity` : `degree(v) + [start=v] + [end=v] = 2·visits(v)`.
* `Bridges.EulerianTrail.odd_degree_vertices_le_two` : At most 2 vertices have odd degree.
-/

namespace Bridges

/-- An Eulerian trail in a multigraph: a walk that traverses every edge exactly once. -/
structure EulerianTrail {nV nE : ℕ} (G : Multigraph nV nE) where
  /-- The sequence of vertices visited. -/
  vertices : Fin (nE + 1) → Fin nV
  /-- The edge used at step `i`. A permutation ensures every edge is used exactly once. -/
  edgePerm : Equiv.Perm (Fin nE)
  /-- At each step, the edge connects consecutive vertices. -/
  connects : ∀ i : Fin nE,
    let e := edgePerm i
    (G.endpt₁ e = vertices i.castSucc ∧ G.endpt₂ e = vertices i.succ) ∨
    (G.endpt₁ e = vertices i.succ ∧ G.endpt₂ e = vertices i.castSucc)

namespace EulerianTrail

variable {nV nE : ℕ} {G : Multigraph nV nE} (t : EulerianTrail G)

/-- The number of times vertex `v` appears in the trail's vertex sequence. -/
def visitCount (v : Fin nV) : ℕ :=
  (Finset.univ.filter (fun j : Fin (nE + 1) => t.vertices j = v)).card

/-- The starting vertex of the trail. -/
def startVertex : Fin nV := t.vertices (0 : Fin (nE + 1))

/-- The ending vertex of the trail. -/
def endVertex : Fin nV := t.vertices (Fin.last nE)

/-- Indicator function: 1 if the proposition holds, 0 otherwise. -/
abbrev ind (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

/-
**Step Count Lemma**: At each step, the count of `v` among edge endpoints
equals the count among consecutive vertices.
-/

/-
The indicator sum over `castSucc` plus the last-vertex indicator equals the visit count.
-/

/-
The indicator sum over `succ` plus the first-vertex indicator equals the visit count.
-/

/-
Reindexing the first endpoint sum through the edge permutation.
-/

/-
Reindexing the second endpoint sum through the edge permutation.
-/

/-
The degree equals the sum of endpoint indicators over all edges.
-/

/-
**Degree–Visit Identity**: `degree(v) + [start=v] + [end=v] = 2·visits(v)`.
-/

/-
Degree has the same parity as the endpoint indicator sum.
-/

end EulerianTrail

/-
**Euler's Parity Theorem**: At most 2 vertices have odd degree in a graph
with an Eulerian trail. This is the necessary condition first discovered
by Euler in 1736.
-/

end Bridges


