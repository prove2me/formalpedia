-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:56:06.529924+00:00
-- url     : https://prove2.me/theorems/d4d2ff2f-8400-446a-8d4e-186156e78298
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable simple graph maximal under drawable supergraphs on the same vertex type has exactly 3|V|−6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      3 * Fintype.card V - 6 = K.edgeFinset.card) := by sorry
