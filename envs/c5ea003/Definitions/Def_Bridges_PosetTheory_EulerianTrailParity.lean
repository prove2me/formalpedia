-- Prove2me | Definitions.Def_Bridges_PosetTheory_EulerianTrailParity
-- name    : Bridges_PosetTheory_EulerianTrailParity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:30.217429+00:00
-- url     : https://prove2.me/theorems/006a1399-f07c-4599-9d91-367d2d667fd7
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_EulerianTrailParity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.EulerianTrailParity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/EulerianTrailParity.lean by skeleton subtraction
import Mathlib

/-!
# Eulerian trails imply at most two odd-degree vertices

This file is a minimal, self-contained formalization of the classical parity
theorem for Eulerian trails on finite multigraphs.

A finite multigraph is encoded by an endpoint map `ends : Fin nE → Fin nV × Fin nV`,
sending each edge index to an *ordered* pair of vertices.  The `degree` of a vertex
is the number of edge endpoints incident to it: each edge contributes `1` for each
of its two endpoints equal to `v`, so a loop at `v` contributes `2`.

An `EulerianTrail` is a walk that uses every edge exactly once: a vertex sequence
`walk : Fin (nE+1) → Fin nV` together with a permutation `edgeAt` of the edges such
that the `i`-th step of the walk traverses edge `edgeAt i` (in either orientation).

The main results are:

* `degree_eq_walk_sum` — the degree of `v` is the sum over walk steps of the number
  of the two consecutive walk positions equal to `v`;
* `degree_add_endpoints` — a telescoping/endpoint-correction identity:
  `degree v + (start-indicator + end-indicator) = 2 * (number of walk positions = v)`;
* `even_degree_of_internal` — a vertex that is neither the start nor the end of the
  trail has even degree;
* `odd_degree_mem_endpoints` — an odd-degree vertex must be the start or the end;
* `odd_degree_vertices_le_two` — there are at most two odd-degree vertices.
-/

namespace EulerianTrailParity

open Finset

/-- A finite multigraph on `nV` vertices and `nE` edges, encoded by an endpoint map
sending each edge to an ordered pair of vertices. -/
structure Multigraph (nV nE : ℕ) where
  /-- The ordered pair of endpoints of each edge. -/
  ends : Fin nE → Fin nV × Fin nV

variable {nV nE : ℕ}

/-- The degree of a vertex `v`: the number of edge endpoints equal to `v`.
Each edge contributes the sum of two indicators (one per endpoint), so a loop at `v`
contributes `2`. -/
def degree (G : Multigraph nV nE) (v : Fin nV) : ℕ :=
  ∑ e : Fin nE,
    ((if (G.ends e).1 = v then 1 else 0) + (if (G.ends e).2 = v then 1 else 0))

/-- An Eulerian trail of `G`: a vertex sequence `walk` together with a permutation
`edgeAt` of the edges, such that the `i`-th step traverses edge `edgeAt i` between the
consecutive walk vertices (in either orientation). -/
structure EulerianTrail (G : Multigraph nV nE) where
  /-- The sequence of `nE + 1` vertices visited by the trail. -/
  walk : Fin (nE + 1) → Fin nV
  /-- The order in which the edges are traversed. -/
  edgeAt : Equiv.Perm (Fin nE)
  /-- The `i`-th step traverses edge `edgeAt i` between `walk i` and `walk (i+1)`. -/
  compat : ∀ i : Fin nE,
    G.ends (edgeAt i) = (walk i.castSucc, walk i.succ) ∨
    G.ends (edgeAt i) = (walk i.succ, walk i.castSucc)

/-
**Degree/incidence identity (A).** The degree of `v` equals the sum, over walk
steps, of the number of the two consecutive walk positions equal to `v`.
-/

/-
**Endpoint-correction identity.** Adding the start and end indicators to the degree
yields twice the number of walk positions equal to `v`.
-/

/-
**(B)** A vertex that is neither the start nor the end of the trail has even degree.
-/

/-
**(C)** Any odd-degree vertex must be the start or the end of the trail.
-/

/-
**(D)** The set of odd-degree vertices has cardinality at most `2`.
-/

end EulerianTrailParity


