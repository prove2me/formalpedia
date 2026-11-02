-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower_of_maximality__p2m_6e927d54_05a0_4e04_9e4a_5cbec6b81d96_a1
-- name    : WilliamsonShmoys.planar_edge_count_lower_of_maximality__p2m_6e927d54_05a0_4e04_9e4a_5cbec6b81d96_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:18:24.605817+00:00
-- url     : https://prove2.me/theorems/71bf5396-ae49-4e3b-9478-7acac339f298
-- title:
--   Maximal drawable graph edge count lower bound
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph on the same vertex set has at least three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_lower_of_maximality__p2m_6e927d54_05a0_4e04_9e4a_5cbec6b81d96_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall U : SimpleGraph V, T <= U -> WilliamsonShmoys.HasPlanarDrawingOn U -> U = T) :
    letI : DecidableRel T.Adj := Classical.decRel T.Adj
    3 * Fintype.card V <= T.edgeFinset.card + 6 := by sorry
