-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:02:24.947222+00:00
-- url     : https://prove2.me/theorems/3eaf26d3-b02e-4c77-b998-3e9af8fb07e7
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V|−6 edges, expressed without subtraction as |E|+6 ≤ 3|V|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
