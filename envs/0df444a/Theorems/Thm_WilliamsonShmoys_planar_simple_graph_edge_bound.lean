-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:49:20.056893+00:00
-- url     : https://prove2.me/theorems/2f87c819-ab51-496e-9d73-f994679a376d
-- title:
--   Edge bound for finite simple planar graphs
-- statement:
--   Every finite simple graph with at least three vertices that has a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
