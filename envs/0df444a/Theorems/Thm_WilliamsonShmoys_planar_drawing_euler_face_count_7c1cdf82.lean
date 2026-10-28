-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_7c1cdf82
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count_7c1cdf82
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:08:32.322242+00:00
-- url     : https://prove2.me/theorems/b2b29c3a-7432-4685-bb67-6067be743389
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with the specified crossing-free drawing has a natural number face count satisfying Euler’s relation. This child removes the drawing-to-embedding and Euler-formula work from the parent; it does not require a lower bound on the vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count_7c1cdf82 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) : Exists fun f : Nat => Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
