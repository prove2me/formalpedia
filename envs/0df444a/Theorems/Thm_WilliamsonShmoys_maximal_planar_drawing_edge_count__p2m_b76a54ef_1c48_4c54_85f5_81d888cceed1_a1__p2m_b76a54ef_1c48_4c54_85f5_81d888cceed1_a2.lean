-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a1__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a1__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:56:24.801557+00:00
-- url     : https://prove2.me/theorems/b0a02e34-0eef-479c-ba08-d5e8c6d2e779
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A maximal simple graph with the specified planar drawing, on at least three vertices, has exactly three times the number of vertices minus six edges. This isolates the topological work from the parent’s finite maximization and witness construction. A proof route is to relate the drawing to a planar embedding with faces, use maximality to establish triangular faces, and apply Euler’s formula and face-edge incidence counting. The remaining core obligation is formalizing these topological steps for the exact arc predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a1__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
