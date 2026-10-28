-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_maximal_drawable_graph_8d131a4d
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_for_maximal_drawable_graph_8d131a4d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:36:50.545439+00:00
-- url     : https://prove2.me/theorems/c2473ef1-1340-467b-9e7a-007cecaf1890
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   A finite simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This removes the ordinary planar edge-count upper-bound argument from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_for_maximal_drawable_graph_8d131a4d
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    (N.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
