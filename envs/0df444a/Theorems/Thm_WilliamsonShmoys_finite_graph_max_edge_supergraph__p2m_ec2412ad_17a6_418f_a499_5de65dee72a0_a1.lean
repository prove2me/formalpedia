-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_max_edge_supergraph__p2m_ec2412ad_17a6_418f_a499_5de65dee72a0_a1
-- name    : WilliamsonShmoys.finite_graph_max_edge_supergraph__p2m_ec2412ad_17a6_418f_a499_5de65dee72a0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:41:21.008783+00:00
-- url     : https://prove2.me/theorems/bc317ffc-480e-4041-b1a9-ff28e2cd4159
-- title:
--   Finite graph maximum edge supergraph
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, if it holds for a graph M, then among the supergraphs of M satisfying the predicate there is one with maximum edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_max_edge_supergraph__p2m_ec2412ad_17a6_418f_a499_5de65dee72a0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hM : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ P N ∧
      ∀ N' : SimpleGraph V, M ≤ N' → P N' →
        (letI : DecidableRel N'.Adj := Classical.decRel N'.Adj
         N'.edgeFinset.card) ≤
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj
         N.edgeFinset.card) := by sorry
