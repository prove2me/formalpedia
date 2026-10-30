-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
-- name    : WilliamsonShmoys.euler_face_count__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:27:18.744582+00:00
-- url     : https://prove2.me/theorems/1954d530-c7a1-4324-8033-8836e3ec1363
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a finite connected graph with the supplied crossing-free drawing, some natural number of faces satisfies Euler’s relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.euler_face_count__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected) :
    ∃ F : ℕ, Fintype.card V + F = H.edgeSet.ncard + 2 := by sorry
