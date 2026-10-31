-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:47.836737+00:00
-- url     : https://prove2.me/theorems/8874575c-8d28-40c2-984e-f8a2d2056536
-- title:
--   Triangulate a finite planar drawing
-- statement:
--   A finite simple graph on at least three vertices with a crossing-free drawing is a subgraph of a graph on the same vertices that also has a crossing-free drawing and exactly 3|V|−6 edges. This isolates the topological augmentation and Euler-counting work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_triangulation__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ T : SimpleGraph V, H ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
