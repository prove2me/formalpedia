-- Prove2me | solution 1 for EulerianParity.Trail.degree_eq_cast_add_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:17:38.71211+00:00
-- url     : https://prove2.me/submissions/fc37fbcf-57f3-4436-b25a-fd36dbc5e6ab

-- Sol generated from Geometry/PosetTheory/EulerianParity.lean
import Mathlib
import Definitions.Def_Geometry_PosetTheory_EulerianParity
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

open EulerianParity

open Finset


variable {nV nE : ℕ}



open Trail

variable {G : Multigraph nV nE}








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







open Trail in
theorem solution: degree G v = T.castCount v + T.succCount v := by
  -- By definition of degree, we can express it as the sum over the edges of the number of times the vertex appears as an endpoint.
  have h_deg : degree G v = ∑ e : Fin nE, (if G.endpt₁ e = v then 1 else 0) + ∑ e : Fin nE, (if G.endpt₂ e = v then 1 else 0) := by
    unfold degree; aesop;
  have h_perm : ∀ e : Fin nE, (if G.endpt₁ (T.edgePerm e) = v then 1 else 0) + (if G.endpt₂ (T.edgePerm e) = v then 1 else 0) = (if T.verts e.castSucc = v then 1 else 0) + (if T.verts e.succ = v then 1 else 0) := by
    intro e; rcases T.adj e with h|h <;> simp +decide [ h ] ;
    ring;
  convert Finset.sum_congr rfl fun e _ => h_perm e using 1;
  any_goals exact Finset.univ;
  · convert h_deg using 1;
    rw [ Finset.sum_add_distrib, Equiv.sum_comp T.edgePerm fun e => if G.endpt₁ e = v then 1 else 0, Equiv.sum_comp T.edgePerm fun e => if G.endpt₂ e = v then 1 else 0 ];
  · unfold Trail.castCount Trail.succCount; simp +decide [ Finset.sum_add_distrib ] ;
