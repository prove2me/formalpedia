-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_retry_2cbac039
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_retry_2cbac039
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:21:53.711265+00:00
-- url     : https://prove2.me/theorems/650b47e8-f5df-4b3a-9472-c92980244f45
-- title:
--   Edge bound for a finite simple planar graph
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_retry_2cbac039 {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
