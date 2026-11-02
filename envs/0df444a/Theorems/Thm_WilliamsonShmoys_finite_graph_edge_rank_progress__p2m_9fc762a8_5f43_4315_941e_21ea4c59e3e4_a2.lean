-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_edge_rank_progress__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
-- name    : WilliamsonShmoys.finite_graph_edge_rank_progress__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:28:43.618216+00:00
-- url     : https://prove2.me/theorems/c664080f-fe5c-4d69-a7a3-cf4803ce0759
-- title:
--   Adding an edge across unreachable vertices increases finite edge rank
-- statement:
--   For a finite vertex type, if the resulting graph's edge set is the original edge set plus the pair of unreachable vertices, then its edge-set cardinality strictly increases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_edge_rank_progress__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (u v : V)
    (hReach : ¬ G.Reachable u v)
    (hEdges : H.edgeSet = G.edgeSet ∪ {Sym2.mk u v}) :
    G.edgeSet.ncard < H.edgeSet.ncard := by sorry
