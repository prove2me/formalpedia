-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:21.320657+00:00
-- url     : https://prove2.me/theorems/799e183d-d2a5-4361-a072-2ee077486503
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite ordered vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ J : SimpleGraph V,
      H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      J = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
