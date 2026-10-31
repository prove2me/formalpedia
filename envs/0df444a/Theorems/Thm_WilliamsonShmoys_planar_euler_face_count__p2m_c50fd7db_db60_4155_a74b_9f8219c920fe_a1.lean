-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_face_count__p2m_c50fd7db_db60_4155_a74b_9f8219c920fe_a1
-- name    : WilliamsonShmoys.planar_euler_face_count__p2m_c50fd7db_db60_4155_a74b_9f8219c920fe_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:56:26.330651+00:00
-- url     : https://prove2.me/theorems/f2fccafe-a945-4eb6-8024-20d186a70be4
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with the supplied crossing-free drawing has a natural number of faces satisfying Euler’s formula. This isolates the conversion from the given drawing to a plane embedding and the Euler characteristic calculation. An independent proof route is to form the embedded graph on the sphere and apply Euler’s formula for connected plane graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_euler_face_count__p2m_c50fd7db_db60_4155_a74b_9f8219c920fe_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hConn : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
