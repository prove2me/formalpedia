-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_count_bound_v2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_edge_count_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:25:15.994116+00:00
-- url     : https://prove2.me/theorems/06232b3e-47c6-453e-bad2-73b1fd81e106
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on its vertex set has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_for_edge_count_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K → K = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
