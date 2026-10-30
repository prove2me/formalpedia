-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulation_edge_count__p2m_b1ccffd4_b471_45dd_901d_142379850b78_a1
-- name    : WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count__p2m_b1ccffd4_b471_45dd_901d_142379850b78_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:16:59.678713+00:00
-- url     : https://prove2.me/theorems/6b40c087-f0a0-4e97-a1ee-42212d56c9dd
-- title:
--   Planar supergraph with triangulation edge count
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count__p2m_b1ccffd4_b471_45dd_901d_142379850b78_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
