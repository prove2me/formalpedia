-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_bound_for_job_f7651c89_84f0_476d_9038_b143112ca155
-- name    : WilliamsonShmoys.exists_planar_supergraph_edge_bound_for_job_f7651c89_84f0_476d_9038_b143112ca155
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:14:36.744985+00:00
-- url     : https://prove2.me/theorems/1741d11a-1189-4036-a189-421ad3678041
-- title:
--   Drawable graphs have a drawable supergraph meeting the planar edge bound
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with at least 3|V| − 6 edges. This child packages completion and the planar edge count; its hypotheses preserve the vertex lower bound needed for triangulation. A concrete route is finite edge-set maximization, proving the maximal drawing is triangulated, then applying Euler’s formula. The topology and counting argument remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_edge_bound_for_job_f7651c89_84f0_476d_9038_b143112ca155
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      Set.Subset L.edgeSet M.edgeSet ∧
      3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
