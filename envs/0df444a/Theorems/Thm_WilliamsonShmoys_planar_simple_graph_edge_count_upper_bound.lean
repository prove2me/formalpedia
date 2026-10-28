-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper_bound
-- name    : WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:13:41.508038+00:00
-- url     : https://prove2.me/theorems/6009196b-f86b-4d84-8003-efa7e8eeee60
-- title:
--   Planar simple graph edge-count upper bound
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has at most 3|V|−6 edges. The vertex-count hypothesis excludes the small cases where this bound is not the planar extremal bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    (G.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
