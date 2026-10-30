-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_edge_count__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:47:05.45213+00:00
-- url     : https://prove2.me/theorems/7d6d0c4a-edbf-4047-8c64-f9e9d27c1695
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable finite simple graph on at least three vertices that admits no proper drawable supergraph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

/-- Euler's formula and triangular faces give the edge count for an inclusion-maximal planar graph. -/

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) (hMax : forall K : SimpleGraph V, G <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = G) : G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
