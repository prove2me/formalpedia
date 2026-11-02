-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_f8b110d8_67db_4582_b9bf_9e52697d207d_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f8b110d8_67db_4582_b9bf_9e52697d207d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:44:53.154908+00:00
-- url     : https://prove2.me/theorems/e087affc-3721-47e3-9583-19a35624e79d
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f8b110d8_67db_4582_b9bf_9e52697d207d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    letI : DecidableRel S.Adj := Classical.decRel S.Adj
    S.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
