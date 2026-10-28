-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_connected_induced_subgraphs__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
-- name    : WilliamsonShmoys.edge_bound_from_connected_induced_subgraphs__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:33:22.427661+00:00
-- url     : https://prove2.me/theorems/e6bd9f62-787a-4dcb-8bdf-b2b862bf0b01
-- title:
--   Combine edge bounds over connected induced subgraphs
-- statement:
--   For a finite simple graph with at least three vertices, if every connected induced subgraph on at least three vertices satisfies the planar edge bound, then the whole graph satisfies it. Prove this by partitioning into connected components, handling components of size one and two directly, and summing the component bounds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_from_connected_induced_subgraphs__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hLocal : ∀ S : Finset V, 3 <= S.card ->
      (G.induce (S : Set V)).Connected ->
      (G.induce (S : Set V)).edgeSet.ncard <= 3 * S.card - 6) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
