-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_for_maximal_drawing_20261026
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_for_maximal_drawing_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:49:48.14579+00:00
-- url     : https://prove2.me/theorems/ba7f0e43-5d2d-471b-881d-54aae946f3cb
-- title:
--   Planar simple graph edge bound for maximal drawings
-- statement:
--   Every finite simple graph with the supplied planar drawing and at least three vertices has at most `3|V| - 6` edges. This supplies the parent's upper bound. The independent proof route is to obtain the planar Euler bound and count face incidences, treating disconnected graphs and small boundary cases explicitly. The remaining core is to connect the supplied arc-based drawing predicate to the combinatorial planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_for_maximal_drawing_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
