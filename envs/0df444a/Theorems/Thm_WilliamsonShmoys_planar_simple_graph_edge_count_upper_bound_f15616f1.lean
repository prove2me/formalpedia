-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper_bound_f15616f1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_f15616f1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:06:05.691436+00:00
-- url     : https://prove2.me/theorems/eaa8e65f-484e-4122-a273-e383810a3b15
-- title:
--   Euler upper bound for a simple drawable graph
-- statement:
--   A drawable simple graph on at least three vertices has at most 3n − 6 edges, whether or not it is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_f15616f1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
