-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1
-- name    : WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:32:32.342231+00:00
-- url     : https://prove2.me/theorems/7f5185ee-24ca-4414-b90e-b6691f6b37ff
-- title:
--   Planar edge count upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
