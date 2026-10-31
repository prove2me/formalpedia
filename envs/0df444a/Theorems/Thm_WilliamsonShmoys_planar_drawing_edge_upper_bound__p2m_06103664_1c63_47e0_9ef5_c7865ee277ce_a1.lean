-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:38.607434+00:00
-- url     : https://prove2.me/theorems/76736e59-4cf5-41fe-b0de-3723f7df5ba6
-- title:
--   Edge upper bound for a finite planar drawing
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
