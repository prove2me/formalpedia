-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_incidence_target
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_for_incidence_target
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:49:25.020888+00:00
-- url     : https://prove2.me/theorems/8c27650b-8ea3-49c2-807f-cf2cc75a14d7
-- title:
--   Simple planar edge bound for the incidence reduction
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied crossing-free drawing has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_for_incidence_target {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) (hV : 3 <= Fintype.card V) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
