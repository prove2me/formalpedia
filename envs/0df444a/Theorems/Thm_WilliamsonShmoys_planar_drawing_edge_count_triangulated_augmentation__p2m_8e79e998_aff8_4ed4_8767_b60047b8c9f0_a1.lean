-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_triangulated_augmentation__p2m_8e79e998_aff8_4ed4_8767_b60047b8c9f0_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_triangulated_augmentation__p2m_8e79e998_aff8_4ed4_8767_b60047b8c9f0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:03:25.544754+00:00
-- url     : https://prove2.me/theorems/ed8fdf3f-bcec-42f4-9879-6d1c022759a1
-- title:
--   Triangulated augmentation of a planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices is contained in a planar supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six. The supergraph certificate supports the target by edge-count monotonicity and arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_triangulated_augmentation__p2m_8e79e998_aff8_4ed4_8767_b60047b8c9f0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
