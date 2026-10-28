-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower_bound_of_inclusion_maximal_job_09cd0f78_596e_4a94_9326_038b3be8d638
-- name    : WilliamsonShmoys.planar_edge_count_lower_bound_of_inclusion_maximal_job_09cd0f78_596e_4a94_9326_038b3be8d638
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:54:20.058178+00:00
-- url     : https://prove2.me/theorems/f7651c89-84f0-476d-9038-b143112ca155
-- title:
--   Maximal drawable graphs meet the planar edge lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on a fixed vertex set of at least three vertices has at least 3|V| − 6 edges. A proof route is to extend the drawing to a triangulation on the same vertices, use maximality to identify the edge sets, and count faces; constructing and counting that completion is the remaining topological obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_lower_bound_of_inclusion_maximal_job_09cd0f78_596e_4a94_9326_038b3be8d638
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset L.edgeSet M.edgeSet ->
      L.edgeSet = M.edgeSet) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry
