-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_edge_maximal_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:58:43.282791+00:00
-- url     : https://prove2.me/theorems/c8cf5b74-b0dc-4b62-8b1d-fc5b28018351
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges (in fact, exactly 3|V|−6).
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_maximal_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hmax : forall T : SimpleGraph V,
      S <= T -> WilliamsonShmoys.HasPlanarDrawingOn T -> T <= S) :
    3 * Fintype.card V <= S.edgeSet.ncard + 6 := by
  sorry
