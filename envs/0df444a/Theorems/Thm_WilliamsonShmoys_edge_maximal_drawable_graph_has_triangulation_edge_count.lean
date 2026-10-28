-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_graph_has_triangulation_edge_count
-- name    : WilliamsonShmoys.edge_maximal_drawable_graph_has_triangulation_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:52:37.438704+00:00
-- url     : https://prove2.me/theorems/ff8faef4-af9a-4072-ac50-7698717ab79c
-- title:
--   An edge-maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on a finite ordered vertex type with at least three vertices has exactly three times the number of vertices minus six edges if it is maximal among drawable supergraphs on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_drawable_graph_has_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ L : SimpleGraph V, M ≤ L → HasPlanarDrawingOn L → L ≤ M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
