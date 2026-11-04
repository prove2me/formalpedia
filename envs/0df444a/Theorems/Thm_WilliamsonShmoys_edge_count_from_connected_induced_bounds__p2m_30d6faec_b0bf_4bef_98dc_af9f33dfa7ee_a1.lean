-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_from_connected_induced_bounds__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1
-- name    : WilliamsonShmoys.edge_count_from_connected_induced_bounds__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:26:12.671406+00:00
-- url     : https://prove2.me/theorems/a488de12-3e96-43d0-9cac-99544200d129
-- title:
--   Assemble edge bounds over connected induced subgraphs
-- statement:
--   For a finite simple graph with at least three vertices, bounds of `3|s| - 6` on every connected induced subgraph of size at least three imply the global `3n - 6` bound. Prove by decomposing into connected components, using the trivial edge counts for components of size one or two, and summing; if every component is small, use the total-size hypothesis directly. This removes disconnected-component bookkeeping from the parent and does not rely on extending the drawing to a connected supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_count_from_connected_induced_bounds__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) (H : SimpleGraph V)
    (hconnBound : ∀ s : Finset V, 3 ≤ s.card →
      (H.induce (↑s : Set V)).Connected →
      letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
      (H.induce (↑s : Set V)).edgeFinset.card ≤ 3 * s.card - 6) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
