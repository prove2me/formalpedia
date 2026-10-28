-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_face_count_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:14:47.975126+00:00
-- url     : https://prove2.me/theorems/e73a1c52-b1e4-4358-a51a-c72566ef2881
-- title:
--   Edge bound for a graph with the supplied planar drawing
-- statement:
--   A simple graph on at least three vertices with the supplied crossing-free drawing has at most three times its vertex count minus six edges. This is the topological graph-counting obligation used to prove the target's facial inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
