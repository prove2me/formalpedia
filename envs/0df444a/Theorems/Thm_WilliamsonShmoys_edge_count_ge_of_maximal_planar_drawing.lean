-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_ge_of_maximal_planar_drawing
-- name    : WilliamsonShmoys.edge_count_ge_of_maximal_planar_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:13:40.61237+00:00
-- url     : https://prove2.me/theorems/a77a98dc-eb9a-4576-95e0-a03e2aa5628e
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   If a graph on at least three vertices has a drawing and no drawable supergraph on the same vertex type can strictly add edges, then it has at least `3n − 6` edges. The boundary `n = 3` is included. The proof route is to extend a drawing to a triangulation on the same vertices: join distinct components with drawable edges, then add noncrossing diagonals in nontriangular faces. Each augmentation gives a drawable supergraph, so maximality forces every added edge to have already belonged to `G`; thus `G` is the triangulation, whose edge count follows from Euler’s formula and face-edge incidence counting. This isolates the maximality and triangulation work from the parent’s arithmetic. It is the main remaining geometric obligation for the reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_ge_of_maximal_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ L : SimpleGraph V, G ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ G) :
    3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by sorry
