-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_count__p2m_899b0d31_5122_4616_b662_d79a2f207d1e_a1
-- name    : WilliamsonShmoys.planar_drawing_completion_edge_count__p2m_899b0d31_5122_4616_b662_d79a2f207d1e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:37:38.644354+00:00
-- url     : https://prove2.me/theorems/e8e38ca1-7bc9-4d8d-a468-0001acb809e9
-- title:
--   Completion of a planar drawing to the maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices can be extended, on the same vertex set, to a drawable graph with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_completion_edge_count__p2m_899b0d31_5122_4616_b662_d79a2f207d1e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
        3 * Fintype.card V = H.edgeFinset.card + 6) := by sorry
