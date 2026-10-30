-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation__p2m_cb4eeb1c_4735_4e17_812d_d7b1036e6d4f_a2
-- name    : WilliamsonShmoys.planar_drawing_triangulation__p2m_cb4eeb1c_4735_4e17_812d_d7b1036e6d4f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:32:25.236032+00:00
-- url     : https://prove2.me/theorems/4b84dc63-4552-46b2-9c09-25aab1a1759e
-- title:
--   Triangulate a finite planar drawing without adding vertices
-- statement:
--   For a finite simple graph with at least three vertices and a crossing-free drawing, there is a triangulated planar supergraph on the same vertex set. It preserves a drawing of the graph, contains every original edge, and has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_triangulation__p2m_cb4eeb1c_4735_4e17_812d_d7b1036e6d4f_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
