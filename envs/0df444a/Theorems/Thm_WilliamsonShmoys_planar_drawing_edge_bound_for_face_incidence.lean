-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_face_incidence
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_for_face_incidence
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T22:35:18.711496+00:00
-- url     : https://prove2.me/theorems/9118e2b8-237f-4a25-b764-cf083375a4f2
-- title:
--   Simple planar edge bound for a face-incidence argument
-- statement:
--   A connected simple graph on at least three vertices with a crossing-free drawing in the plane has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_for_face_incidence
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
