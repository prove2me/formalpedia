-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_upper_bound__p2m_267a842e_101e_4cf6_b705_d11d92433d33_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound__p2m_267a842e_101e_4cf6_b705_d11d92433d33_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:04:25.598507+00:00
-- url     : https://prove2.me/theorems/e844fca5-030a-4b1e-8670-0e19dfc2fff4
-- title:
--   Planar edge-count upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound__p2m_267a842e_101e_4cf6_b705_d11d92433d33_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V) :
    (letI : DecidableRel H.Adj := dH;
     H.edgeFinset.card <= 3 * Fintype.card V - 6) := by sorry
