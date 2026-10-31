-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:22:00.834463+00:00
-- url     : https://prove2.me/theorems/cb4eeb1c-4735-4e17-812d-d7b1036e6d4f
-- title:
--   Simple planar graph edge bound from a crossing-free drawing
-- statement:
--   A finite simple graph with at least three vertices and the supplied crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
