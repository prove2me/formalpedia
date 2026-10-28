-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count_planar_edge_bound_4d0c2802_8f3b_4d79_b31d_d0704c9c8543
-- name    : WilliamsonShmoys.euler_face_count_planar_edge_bound_4d0c2802_8f3b_4d79_b31d_d0704c9c8543
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:30:17.057176+00:00
-- url     : https://prove2.me/theorems/fd1134b3-ad9d-4bda-a008-b617586c2649
-- title:
--   Simple planar edge bound from the supplied drawing
-- statement:
--   A finite connected simple graph on at least three vertices with the supplied crossing-free drawing has at most three times its vertex count minus six edges. Combined with the target’s Euler equation, this yields the target incidence inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_count_planar_edge_bound_4d0c2802_8f3b_4d79_b31d_d0704c9c8543 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
