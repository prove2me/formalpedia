-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:18:51.38198+00:00
-- url     : https://prove2.me/theorems/6374a222-b9ca-4739-aa07-1f48fa42cfcc
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   An inclusion-maximal graph admitting the specified planar drawing, with at least three vertices, has at least 3|V| − 6 edges. Maximality forces a triangulation; Euler’s formula and face-edge incidence counting yield the bound, with K₃ as the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : ∀ Z : SimpleGraph V,
      Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) :
    3 * Fintype.card V ≤ Y.edgeSet.ncard + 6 := by sorry
