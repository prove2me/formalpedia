-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_edge_rank_bound__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
-- name    : WilliamsonShmoys.finite_graph_edge_rank_bound__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:28:48.86606+00:00
-- url     : https://prove2.me/theorems/aa78a1e2-d033-4093-bc4f-e6e8bfea001a
-- title:
--   Finite graph edge rank is bounded by the number of vertex pairs
-- statement:
--   For a finite vertex type, the number of edges in a simple graph is at most the number of unordered vertex pairs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_edge_rank_bound__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
    {V : Type} [Fintype V] (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by sorry
