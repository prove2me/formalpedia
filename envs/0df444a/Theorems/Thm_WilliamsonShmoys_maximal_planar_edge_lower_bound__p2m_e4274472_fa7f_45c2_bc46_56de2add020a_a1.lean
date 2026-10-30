-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:11.163993+00:00
-- url     : https://prove2.me/theorems/1479c9f9-4504-425f-aa40-f345c4f3c928
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      3 * Fintype.card V - 6 ≤ H.edgeFinset.card) := by sorry
