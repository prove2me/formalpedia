-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_edge_bound_20261028
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count_edge_bound_20261028
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:01:16.023909+00:00
-- url     : https://prove2.me/theorems/077a4339-4bbf-421b-a406-ee02e14312b8
-- title:
--   Euler face count and boundary inequality from a planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and the given crossing-free drawing, there is a finite face count satisfying Euler’s equation and the aggregate lower bound of three on facial boundary lengths.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_count_edge_bound_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ F : ℕ, Fintype.card V + F = G.edgeSet.ncard + 2 ∧
      3 * F ≤ 2 * G.edgeSet.ncard := by sorry
