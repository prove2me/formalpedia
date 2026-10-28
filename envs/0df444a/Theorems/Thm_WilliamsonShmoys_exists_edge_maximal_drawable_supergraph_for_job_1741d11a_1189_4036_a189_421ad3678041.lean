-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph_for_job_1741d11a_1189_4036_a189_421ad3678041
-- name    : WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_for_job_1741d11a_1189_4036_a189_421ad3678041
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:40:48.597694+00:00
-- url     : https://prove2.me/theorems/326db4b4-eabd-4e86-b876-ccbf99bd7b34
-- title:
--   Every drawable graph has an edge-maximal drawable supergraph
-- statement:
--   A drawable finite graph has a drawable supergraph on the same vertices that admits no strict drawable supergraph. The original graph is feasible, and there are finitely many simple graphs on the vertex type, so one can choose a feasible graph with a maximal edge set. This removes finite maximization from the parent. It does not claim that the chosen graph is triangulated or has the required edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_for_job_1741d11a_1189_4036_a189_421ad3678041
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      Set.Subset L.edgeSet M.edgeSet ∧
      ∀ N : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn N →
        Set.Subset M.edgeSet N.edgeSet →
        Set.Subset N.edgeSet M.edgeSet := by sorry
