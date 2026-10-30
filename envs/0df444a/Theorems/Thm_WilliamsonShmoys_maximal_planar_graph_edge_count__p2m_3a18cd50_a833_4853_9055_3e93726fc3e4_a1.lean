-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:50:04.043778+00:00
-- url     : https://prove2.me/theorems/9e9ddd37-2fbe-4f2e-b4a6-63a4b0058d20
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
