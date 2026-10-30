-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count_retry2
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:09:48.501506+00:00
-- url     : https://prove2.me/theorems/f9cbd8b9-e96b-443f-8c6b-5c3a6e04fc5c
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly $3|V|-6$ edges. This supplies the edge-count conclusion needed by the parent. An independent proof route is to show that maximality forces a planar embedding to be connected and every face boundary to be a triangle, then apply Euler’s formula and count face-edge incidences. The hypothesis $3 \le |V|$ is essential for this triangulation count, and the arc-drawing predicate makes recovering the required face structure the main formalization obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hWdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall X : SimpleGraph V, W <= X ->
      WilliamsonShmoys.HasPlanarDrawingOn X -> X <= W) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by sorry
