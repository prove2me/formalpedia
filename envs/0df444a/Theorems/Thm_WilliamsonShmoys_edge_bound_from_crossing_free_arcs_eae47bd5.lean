-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_crossing_free_arcs_eae47bd5
-- name    : WilliamsonShmoys.edge_bound_from_crossing_free_arcs_eae47bd5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:44:20.453023+00:00
-- url     : https://prove2.me/theorems/014ba93e-27d6-4424-99f6-daebb07fc320
-- title:
--   Planar edge bound from crossing-free arcs
-- statement:
--   A connected simple graph with at least three vertices and the supplied crossing-free arc drawing has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_bound_from_crossing_free_arcs_eae47bd5
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
