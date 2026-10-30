-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_edge_count__p2m_799e183d_d2a5_4361_a072_2ee077486503_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_edge_count__p2m_799e183d_d2a5_4361_a072_2ee077486503_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:04:36.353463+00:00
-- url     : https://prove2.me/theorems/5c3e2d4d-9b9a-4ad6-be37-e52a0ce51388
-- title:
--   Edge count of a maximal planar extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices extends, on that same vertex type, to a drawable graph with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_maximal_extension_edge_count__p2m_799e183d_d2a5_4361_a072_2ee077486503_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
