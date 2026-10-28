-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_faces
-- name    : WilliamsonShmoys.planar_drawing_euler_faces
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:03:47.229266+00:00
-- url     : https://prove2.me/theorems/e3a1eb23-1066-443b-8543-45a066ee1eb8
-- title:
--   Euler face count from a connected planar drawing
-- statement:
--   A connected graph with the supplied crossing-free plane drawing has a natural face count satisfying Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_faces
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun f : Nat => K.edgeSet.ncard + 2 = Fintype.card V + f := by sorry
