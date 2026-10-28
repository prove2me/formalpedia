-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_job_d022b1d1_d1e3_4932_940e_a619c500f998
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count_job_d022b1d1_d1e3_4932_940e_a619c500f998
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:26:13.553979+00:00
-- url     : https://prove2.me/theorems/b05b772b-af13-4e3c-932e-049c7f8aba69
-- title:
--   Euler face count for a connected plane drawing
-- statement:
--   A finite connected graph with the supplied plane drawing has a natural face count satisfying Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count_job_d022b1d1_d1e3_4932_940e_a619c500f998 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) : ∃ f : Nat, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
