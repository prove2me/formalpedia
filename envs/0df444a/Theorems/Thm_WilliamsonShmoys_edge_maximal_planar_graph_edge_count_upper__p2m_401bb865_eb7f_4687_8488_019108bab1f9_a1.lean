-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count_upper__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_edge_count_upper__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:11.345198+00:00
-- url     : https://prove2.me/theorems/ad02c9e2-6f74-49a1-ae0d-05fd18f8b6b9
-- title:
--   Euler upper bound for planar graph edges
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_edge_count_upper__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
