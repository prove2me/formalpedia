-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
-- name    : WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:37:45.418061+00:00
-- url     : https://prove2.me/theorems/dc457ca2-cc5d-4b3b-81b3-dc716865aa77
-- title:
--   Upper edge bound for a planar drawing
-- statement:
--   Every simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel G.Adj := dG
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
