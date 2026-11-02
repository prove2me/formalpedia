-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_2a34f2f7_4575_4fc5_979a_579be47b545a_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_2a34f2f7_4575_4fc5_979a_579be47b545a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:40:38.580918+00:00
-- url     : https://prove2.me/theorems/f8447601-6d74-49c3-87d5-1aada8b2c48f
-- title:
--   Simple planar graphs have at most 3n−6 edges
-- statement:
--   A drawable simple graph on at least three finite linearly ordered vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_2a34f2f7_4575_4fc5_979a_579be47b545a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
