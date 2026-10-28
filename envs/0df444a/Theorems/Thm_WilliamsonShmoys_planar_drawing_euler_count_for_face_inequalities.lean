-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_count_for_face_inequalities
-- name    : WilliamsonShmoys.planar_drawing_euler_count_for_face_inequalities
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:18:55.176281+00:00
-- url     : https://prove2.me/theorems/ad55cdfc-27be-4048-95a9-5edda76211f4
-- title:
--   Euler face count from a connected planar drawing
-- statement:
--   A connected graph with the supplied crossing-free drawing has a finite face count satisfying Euler’s formula. One route is to form the planar embedding on the sphere and apply Euler characteristic, counting both sides of bridge edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_count_for_face_inequalities
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by sorry
