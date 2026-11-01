-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_max_edge_ncard__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_max_edge_ncard__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:53:56.642357+00:00
-- url     : https://prove2.me/theorems/e49dd89d-d108-495e-8d00-dca20abd3296
-- title:
--   Maximum-edge drawable supergraph
-- statement:
--   Among the drawable supergraphs of L on the same finite vertex type, there is one whose edge set has maximum cardinality. The candidate family is nonempty because L belongs to it. This isolates the finite maximization step from the conversion of maximum cardinality into inclusion-maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_planar_supergraph_max_edge_ncard__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        L ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
