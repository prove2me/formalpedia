-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:25.676451+00:00
-- url     : https://prove2.me/theorems/a74b4731-eea6-44e0-b9ad-6ea707b8b09a
-- title:
--   Edge bound for a planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
