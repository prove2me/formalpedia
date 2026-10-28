-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_bcd4e9c3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_bcd4e9c3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:02:02.682979+00:00
-- url     : https://prove2.me/theorems/1369a85c-de52-482a-8533-764f028fa057
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices with no proper drawable supergraph has exactly $3|V|-6$ edges. The proof must establish that maximality forces a triangulated plane embedding and then apply Euler's formula. The vertex lower bound is needed for this edge-count conclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_bcd4e9c3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
