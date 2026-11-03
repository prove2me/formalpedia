-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:08:21.360206+00:00
-- url     : https://prove2.me/theorems/b0556792-8fbb-42b1-83f9-e49450aba15a
-- title:
--   Simple planar edge bound from a crossing-free drawing
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges, expressed without truncated subtraction. A proof route is to use the planar map from the drawing, count edge sides along facial boundary walks, and apply the lower bound of three on total facial boundary length, treating bridges as contributing both sides. The vertex-count hypothesis preserves the standard small-order boundary condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
