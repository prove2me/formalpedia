-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_graph_edge_count_completion__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2
-- name    : WilliamsonShmoys.simple_graph_edge_count_completion__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:10:18.913912+00:00
-- url     : https://prove2.me/theorems/2d289b42-b746-4ae0-ab0c-c0dc410cd004
-- title:
--   Extend a finite simple graph to an exact feasible edge count
-- statement:
--   If a finite simple graph has at most m edges and m is no greater than the number of unordered pairs of distinct vertices, extend it to a supergraph with exactly m edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.simple_graph_edge_count_completion__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (m : Nat)
    (hG : letI : DecidableRel G.Adj := Classical.decRel G.Adj
      G.edgeFinset.card ≤ m)
    (hcap : m ≤ Nat.choose (Fintype.card V) 2) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card = m) := by sorry
