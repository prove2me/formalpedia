-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:00:44.345398+00:00
-- url     : https://prove2.me/theorems/ac724374-f88c-4ddf-bad5-42fda9b092d4
-- title:
--   Lower bound from maximal drawable supergraph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertex type has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    letI : DecidableRel S.Adj := Classical.decRel S.Adj
    3 * Fintype.card V ≤ S.edgeFinset.card + 6 := by sorry
