-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_42a68497_1fb0_460d_90d9_a7891ca5f267_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_42a68497_1fb0_460d_90d9_a7891ca5f267_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T19:24:11.663711+00:00
-- url     : https://prove2.me/theorems/fd3a6d21-9f96-42df-ba7f-14589e74085f
-- title:
--   Drawable graphs have an exact planar edge-count completion
-- statement:
--   Every drawable finite simple graph on at least three vertices can be extended on the same vertex set to a drawable graph whose edge count plus six equals three times the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_42a68497_1fb0_460d_90d9_a7891ca5f267_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      Set.Subset G.edgeSet K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
