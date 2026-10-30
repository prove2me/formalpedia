-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_euler_inequalities
-- name    : WilliamsonShmoys.planar_drawing_face_count_euler_inequalities
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:04:10.569977+00:00
-- url     : https://prove2.me/theorems/359ea9f3-5bdc-4a0f-8549-d68edc39aef6
-- title:
--   Euler and facial boundary count for a connected planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and the supplied crossing-free drawing, there is a finite face count f satisfying Euler’s equation V + f = E + 2, and the total facial boundary length is at least three per face, while equaling twice the number of edges. Bridges contribute both directed sides.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count_euler_inequalities
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f <= 2 * K.edgeSet.ncard := by sorry
