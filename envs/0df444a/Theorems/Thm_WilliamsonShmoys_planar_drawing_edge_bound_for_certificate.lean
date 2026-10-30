-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_certificate
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_for_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:24:23.515872+00:00
-- url     : https://prove2.me/theorems/847b07c4-bc5d-43bb-ad3d-c9e57f9afa3a
-- title:
--   Simple planar edge bound for a drawn graph
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges, expressed without natural subtraction. A proof route is to use the drawing’s plane embedding, count two facial boundary incidences per edge (including bridges), establish that each face boundary has length at least three, and combine the resulting incidence bound with Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_for_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
