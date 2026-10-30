-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:16:01.225742+00:00
-- url     : https://prove2.me/theorems/ec3e03f0-5758-464a-8536-b42e2e8ffdc8
-- title:
--   Edge bound for an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
