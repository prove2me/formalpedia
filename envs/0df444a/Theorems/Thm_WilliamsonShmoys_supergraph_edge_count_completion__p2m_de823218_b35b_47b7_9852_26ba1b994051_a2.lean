-- Prove2me | Theorems.Thm_WilliamsonShmoys_supergraph_edge_count_completion__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
-- name    : WilliamsonShmoys.supergraph_edge_count_completion__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:07:26.844033+00:00
-- url     : https://prove2.me/theorems/3be8fb19-1696-42e0-add6-8cf83fd59ba5
-- title:
--   Complete a finite graph to a permitted edge count
-- statement:
--   Extend the graph to a supergraph whose edge count lies between n−2 and 3n−6, inclusive.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.supergraph_edge_count_completion__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hbound : letI : DecidableRel G.Adj := Classical.decRel G.Adj
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       Fintype.card V - 2 ≤ H.edgeFinset.card ∧
       H.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
