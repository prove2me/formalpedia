-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_6f9002e1_e01e_4c8a_bc92_8342a46a38e8_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_6f9002e1_e01e_4c8a_bc92_8342a46a38e8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:36:12.03618+00:00
-- url     : https://prove2.me/theorems/c756091c-f70a-448d-aae8-42ee8ba967ba
-- title:
--   Edge bound for a finite simple planar graph
-- statement:
--   Every finite simple graph with at least three vertices that admits the given crossing-free planar drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_6f9002e1_e01e_4c8a_bc92_8342a46a38e8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    [DecidableRel G.Adj] :
    G.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
