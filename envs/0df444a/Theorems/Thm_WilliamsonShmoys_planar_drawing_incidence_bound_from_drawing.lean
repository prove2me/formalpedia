-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_incidence_bound_from_drawing
-- name    : WilliamsonShmoys.planar_drawing_incidence_bound_from_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:24:42.464629+00:00
-- url     : https://prove2.me/theorems/b4124831-0c15-4632-b642-7fb3fafb3aeb
-- title:
--   Facial incidence bound from a simple planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and the supplied planar drawing, any natural number satisfying the Euler count is bounded by the total number of edge sides.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_incidence_bound_from_drawing {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) (hV : 3 <= Fintype.card V) (f : ℕ) (hEuler : Fintype.card V + f = G.edgeSet.ncard + 2) : 3 * f <= 2 * G.edgeSet.ncard := by sorry
