-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound_e51c1790
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_lower_bound_e51c1790
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:44:31.560816+00:00
-- url     : https://prove2.me/theorems/303ecbff-d1f8-46a6-a9e1-da5ad5ea0381
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable supergraph inclusion has at least 3|V|−6 edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_lower_bound_e51c1790
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V,
      U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U) :
    3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by sorry
