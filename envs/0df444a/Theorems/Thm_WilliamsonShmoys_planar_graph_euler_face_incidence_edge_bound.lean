-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_euler_face_incidence_edge_bound
-- name    : WilliamsonShmoys.planar_graph_euler_face_incidence_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:37:11.541005+00:00
-- url     : https://prove2.me/theorems/3c186683-4aab-4112-b37e-6e32db24902a
-- title:
--   Planar edge bound for a connected drawn graph
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most three times its number of vertices minus six edges. The independent proof route uses a plane embedding, Euler's formula, and the fact that each face boundary has at least three edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_euler_face_incidence_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
