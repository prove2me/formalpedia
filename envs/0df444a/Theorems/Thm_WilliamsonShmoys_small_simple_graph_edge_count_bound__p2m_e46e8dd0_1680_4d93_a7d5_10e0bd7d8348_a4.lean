-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_simple_graph_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4
-- name    : WilliamsonShmoys.small_simple_graph_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:23:58.970714+00:00
-- url     : https://prove2.me/theorems/f6e6c4ad-3b22-43a2-b744-06e0b19b3166
-- title:
--   Edge count for graphs with fewer than three vertices
-- statement:
--   A simple graph on fewer than three vertices has at most half its vertex count in edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.small_simple_graph_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4 {V : Type} [Fintype V] (G : SimpleGraph V) (hCard : Fintype.card V < 3) : G.edgeSet.ncard <= Fintype.card V / 2 := by sorry
