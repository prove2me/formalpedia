-- Prove2me | Definitions.Def_Geometry_PosetTheory_EulerianParity
-- name    : Geometry_PosetTheory_EulerianParity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:37.160698+00:00
-- url     : https://prove2.me/theorems/05da6c49-b07f-4300-829f-4dce3b2ae761
-- title:
--   Aether Catalog definitions — Geometry_PosetTheory_EulerianParity
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PosetTheory.EulerianParity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PosetTheory/EulerianParity.lean by skeleton subtraction
import Mathlib
/-
# Eulerian trails: the classical parity theorem

A small, self-contained development of the parity (handshake-style) theorem for
Eulerian trails in finite undirected multigraphs **with loops**.

## Model

* `Multigraph nV nE` is a finite multigraph on vertex set `Fin nV` with edge set
  `Fin nE`, given by two endpoint maps `endpt₁ endpt₂ : Fin nE → Fin nV`.
  A loop is an edge `e` with `endpt₁ e = endpt₂ e`.

* `degree G v` counts endpoint incidences at `v`, summing over **both** endpoint
  slots; hence a loop at `v` contributes `2`.

* `Trail G` is an Eulerian trail: a vertex walk `verts : Fin (nE+1) → Fin nV`
  together with a permutation `edgePerm` of the edges (so every edge is used
  exactly once) and a proof `adj` that the `i`-th step traverses edge
  `edgePerm i` between `verts i.castSucc` and `verts i.succ`, in either
  orientation.

## Main results

1. `Trail.parity_identity` — the local counting identity at every vertex `v`:
   `degree G v + startIndicator v + endIndicator v = 2 * visitCount v`.
   The proof is pure finite counting: each internal visit contributes two
   incidences, each endpoint one.

2. `Trail.odd_degree_isEndpoint` — if `Odd (degree G v)` then `v` is the start
   or the end vertex of the trail.

3. `Trail.card_oddDegree_le_two` — at most two vertices have odd degree.

4. `Trail.closed_even_degree` — if the trail is closed (start = end) then every
   vertex has even degree.
-/

namespace EulerianParity

open Finset

/-- A finite undirected multigraph with loops: vertices `Fin nV`, edges `Fin nE`,
and two endpoint maps. -/
structure Multigraph (nV nE : ℕ) where
  endpt₁ : Fin nE → Fin nV
  endpt₂ : Fin nE → Fin nV

variable {nV nE : ℕ}

/-- The degree of `v`: the number of endpoint incidences equal to `v`, counting
both endpoint slots. A loop at `v` contributes `2`. -/
def degree (G : Multigraph nV nE) (v : Fin nV) : ℕ :=
  (univ.filter (fun e => G.endpt₁ e = v)).card +
  (univ.filter (fun e => G.endpt₂ e = v)).card

/-- An Eulerian trail: a vertex walk using every edge exactly once. -/
structure Trail (G : Multigraph nV nE) where
  /-- The walk of `nE + 1` vertices. -/
  verts : Fin (nE + 1) → Fin nV
  /-- The order in which the edges are traversed (each edge exactly once). -/
  edgePerm : Equiv.Perm (Fin nE)
  /-- Step `i` traverses edge `edgePerm i` between consecutive walk vertices,
  in either orientation. -/
  adj : ∀ i : Fin nE,
      (G.endpt₁ (edgePerm i) = verts i.castSucc ∧ G.endpt₂ (edgePerm i) = verts i.succ) ∨
      (G.endpt₁ (edgePerm i) = verts i.succ ∧ G.endpt₂ (edgePerm i) = verts i.castSucc)

namespace Trail

variable {G : Multigraph nV nE}

/-- The starting vertex of the trail. -/
def start (T : Trail G) : Fin nV := T.verts 0

/-- The ending vertex of the trail. -/
def last (T : Trail G) : Fin nV := T.verts (Fin.last nE)

/-- The number of times the walk visits `v` (over all `nE + 1` positions). -/
def visitCount (T : Trail G) (v : Fin nV) : ℕ :=
  ∑ j : Fin (nE + 1), (if T.verts j = v then 1 else 0)

/-- `1` if `v` is the start vertex, else `0`. -/
def startIndicator (T : Trail G) (v : Fin nV) : ℕ :=
  if T.verts 0 = v then 1 else 0

/-- `1` if `v` is the end vertex, else `0`. -/
def endIndicator (T : Trail G) (v : Fin nV) : ℕ :=
  if T.verts (Fin.last nE) = v then 1 else 0

/-- Count of steps whose *first* (castSucc) walk vertex equals `v`. -/
def castCount (T : Trail G) (v : Fin nV) : ℕ :=
  ∑ i : Fin nE, (if T.verts i.castSucc = v then 1 else 0)

/-- Count of steps whose *second* (succ) walk vertex equals `v`. -/
def succCount (T : Trail G) (v : Fin nV) : ℕ :=
  ∑ i : Fin nE, (if T.verts i.succ = v then 1 else 0)

variable (T : Trail G) (v : Fin nV)

/-
Splitting the walk at its last vertex.
-/

/-
Splitting the walk at its first vertex.
-/

/-
The degree of `v` equals the number of consecutive walk pairs incident to
`v` (first slot plus second slot). This is where the edge permutation and the
adjacency condition are used.
-/





end Trail

end EulerianParity


