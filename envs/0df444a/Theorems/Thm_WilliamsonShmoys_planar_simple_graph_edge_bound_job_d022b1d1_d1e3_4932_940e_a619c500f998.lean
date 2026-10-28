-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_job_d022b1d1_d1e3_4932_940e_a619c500f998
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_job_d022b1d1_d1e3_4932_940e_a619c500f998
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:32:33.308232+00:00
-- url     : https://prove2.me/theorems/fe21991c-ced2-4264-b0ba-48a28e46de2d
-- title:
--   Edge bound for a simple plane graph
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied plane drawing has at most 3n - 6 edges, stated without natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_job_d022b1d1_d1e3_4932_940e_a619c500f998 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) (hV : 3 <= Fintype.card V) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
