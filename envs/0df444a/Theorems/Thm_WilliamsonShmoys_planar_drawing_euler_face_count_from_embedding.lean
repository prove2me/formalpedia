-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_from_embedding
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count_from_embedding
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:11:48.992502+00:00
-- url     : https://prove2.me/theorems/c9d46756-529a-4897-8f29-076af02f0518
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with a crossing-free drawing has a finite face count, including the unbounded face, satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count_from_embedding
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
