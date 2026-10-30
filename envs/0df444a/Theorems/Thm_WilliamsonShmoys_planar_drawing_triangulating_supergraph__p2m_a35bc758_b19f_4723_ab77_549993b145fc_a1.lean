-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulating_supergraph__p2m_a35bc758_b19f_4723_ab77_549993b145fc_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulating_supergraph__p2m_a35bc758_b19f_4723_ab77_549993b145fc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T13:13:03.595334+00:00
-- url     : https://prove2.me/theorems/5eb931ac-62c5-416c-b76b-d99787ed9024
-- title:
--   Triangulating supergraph of a planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a crossing-free simple supergraph on the same vertices with exactly 3n−6 edges; its edge set contains the original edge set, so the original edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulating_supergraph__p2m_a35bc758_b19f_4723_ab77_549993b145fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
