-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_from_faces
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_from_faces
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:47:15.614973+00:00
-- url     : https://prove2.me/theorems/7c26b4e8-59da-4b61-8645-9586bd504461
-- title:
--   Simple planar edge bound from facial incidence counting
-- statement:
--   A finite connected simple graph on at least three vertices with the supplied crossing-free drawing has at most 3n − 6 edges. Prove this using Euler’s formula and facial edge-side counting, with simplicity and the vertex lower bound ensuring each face boundary walk has length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_from_faces
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
