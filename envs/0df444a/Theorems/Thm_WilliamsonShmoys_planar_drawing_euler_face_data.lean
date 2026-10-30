-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data
-- name    : WilliamsonShmoys.planar_drawing_euler_face_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:51:55.535989+00:00
-- url     : https://prove2.me/theorems/9e11ae8d-a304-4350-b8b9-3d00499e16f8
-- title:
--   Euler count and facial incidence bound from a planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and the supplied crossing-free drawing, there is a natural number of faces satisfying the connected Euler count and the total facial incidence lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_data {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) (hV : 3 <= Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧ 3 * f <= 2 * G.edgeSet.ncard := by sorry
