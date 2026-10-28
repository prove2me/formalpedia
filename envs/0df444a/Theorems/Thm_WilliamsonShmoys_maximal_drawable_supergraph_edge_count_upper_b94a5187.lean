-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count_upper_b94a5187
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_edge_count_upper_b94a5187
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:48:39.940438+00:00
-- url     : https://prove2.me/theorems/d31f4647-0073-4c1c-a184-e25d682bd699
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   A graph with a planar drawing on at least three vertices has at most `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_edge_count_upper_b94a5187
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
