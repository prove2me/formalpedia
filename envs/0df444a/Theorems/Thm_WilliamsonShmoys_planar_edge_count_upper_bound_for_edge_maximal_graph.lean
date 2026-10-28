-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_edge_maximal_graph
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_for_edge_maximal_graph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:04:08.34932+00:00
-- url     : https://prove2.me/theorems/c61b3391-988b-4f33-aca8-45f8792ca5e8
-- title:
--   Euler edge bound for finite simple planar graphs
-- statement:
--   Every finite simple planar graph with at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_for_edge_maximal_graph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
