-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_connected_induced_subgraphs__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
-- name    : WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:07:45.847205+00:00
-- url     : https://prove2.me/theorems/91fdce47-b3a5-46de-8589-e108dd79c43e
-- title:
--   Combine edge bounds over connected induced subgraphs
-- statement:
--   If every connected induced subgraph on at least three vertices satisfies the planar simple-graph edge bound, then the whole finite simple graph on at least three vertices satisfies it. Decompose into connected components; components of size one or two contribute zero or at most one edge, while each larger component contributes at most three times its size minus six. Summing gives the claimed bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hconnBound : ∀ (s : Finset V), 3 ≤ s.card →
      (G.induce (↑s : Set V)).Connected →
      (letI : DecidableRel (G.induce (↑s : Set V)).Adj :=
        Classical.decRel (G.induce (↑s : Set V)).Adj
       (G.induce (↑s : Set V)).edgeFinset.card ≤
         3 * Fintype.card (↑(s : Set V)) - 6)) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
