-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_from_arcs
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_from_arcs
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:10:24.394675+00:00
-- url     : https://prove2.me/theorems/8efe11c9-488d-485e-9192-90e34a0f24b5
-- title:
--   Simple planar edge bound from an arc drawing
-- statement:
--   A connected simple graph with at least three vertices and the supplied crossing-free drawing has at most 3|V|−6 edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_from_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
