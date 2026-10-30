-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_for_triangulating_extension_8070196b
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count_for_triangulating_extension_8070196b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:05:52.759596+00:00
-- url     : https://prove2.me/theorems/053a8a16-0e0e-43b8-a75d-62a926ce2bdc
-- title:
--   A maximal drawable supergraph has exactly 3n − 6 edges
-- statement:
--   If a drawable graph on at least three vertices is maximal among drawable supergraphs on those vertices, then it has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count_for_triangulating_extension_8070196b
    {V : Type} [Fintype V] [LinearOrder V]
    (T U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hTU : T.edgeSet ⊆ U.edgeSet)
    (hU : HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V,
      U.edgeSet ⊆ W.edgeSet →
      HasPlanarDrawingOn W →
      W.edgeSet ⊆ U.edgeSet) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
