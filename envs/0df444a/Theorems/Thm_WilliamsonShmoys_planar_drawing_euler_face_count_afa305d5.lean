-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_afa305d5
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count_afa305d5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T14:00:08.081724+00:00
-- url     : https://prove2.me/theorems/7174d599-bce7-43d0-af78-784ca25f09d3
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a finite connected graph with a crossing-free drawing as defined by `HasPlanarDrawingOn`, the number of complementary faces satisfies Euler’s relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count_afa305d5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConn : H.Connected) :
    exists f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
