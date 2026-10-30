-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_and_face_degree_bound
-- name    : WilliamsonShmoys.planar_drawing_euler_and_face_degree_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:02:10.768847+00:00
-- url     : https://prove2.me/theorems/d022b1d1-d1e3-4932-940e-a619c500f998
-- title:
--   Euler and face-degree bounds for a simple plane drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and the supplied crossing-free drawing, there is a finite face count f satisfying Euler’s formula and the standard lower bound on total facial boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_and_face_degree_bound {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) (hV : 3 <= Fintype.card V) : ∃ f : Nat, Fintype.card V + f = G.edgeSet.ncard + 2 ∧ 3 * f <= 2 * G.edgeSet.ncard := by sorry
