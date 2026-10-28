-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_e51c1790
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_e51c1790
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:10:50.048946+00:00
-- url     : https://prove2.me/theorems/b2a02696-52d5-446b-addf-7d7ee811ddc9
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable supergraph inclusion has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_e51c1790
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V,
      U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U) :
    3 * Fintype.card V = U.edgeSet.ncard + 6 := by sorry
