-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:04:52.382307+00:00
-- url     : https://prove2.me/theorems/37333af2-96a7-4204-9288-5c1c69b149fa
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V| − 6 edges. The proof must establish that maximality forces a triangulation, then use Euler’s formula and count face-edge incidences; the three-vertex boundary case is K₃.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_dabb2cbe_7fe3_4213_96ba_204afbbd922b
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : ∀ Z : SimpleGraph V,
      Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) :
    3 * Fintype.card V = Y.edgeSet.ncard + 6 := by sorry
