-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_face_count
-- name    : WilliamsonShmoys.planar_euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:06:35.690087+00:00
-- url     : https://prove2.me/theorems/08fc31d6-80fd-42a5-a763-84103286bb7f
-- title:
--   Euler face count for a connected drawable graph
-- statement:
--   A finite connected graph with the specified crossing-free drawing has a natural number of complementary faces, counting the unbounded face, satisfying Euler’s formula. Connectedness is required for this form. A proof can derive Euler’s formula for a finite plane embedding and identify its face count with a natural number; this supplies the parent’s equality. The remaining obligation is to develop or formalize face counting for the drawing representation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hConn : K.Connected) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by sorry
