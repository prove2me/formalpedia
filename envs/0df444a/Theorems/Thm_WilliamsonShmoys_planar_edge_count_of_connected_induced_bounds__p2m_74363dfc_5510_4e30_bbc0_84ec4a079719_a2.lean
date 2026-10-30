-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_connected_induced_bounds__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
-- name    : WilliamsonShmoys.planar_edge_count_of_connected_induced_bounds__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:28:55.325983+00:00
-- url     : https://prove2.me/theorems/7d0b953f-c62a-470f-b8ef-9a25b50c3ad5
-- title:
--   Aggregate connected induced-subgraph bounds
-- statement:
--   If every connected induced subgraph satisfies the stated local edge bound, then a graph with at least three vertices satisfies the global planar edge bound. This removes component bookkeeping from the parent. A proof route partitions the edge set by connected components, applies the local estimate to each component, uses zero edges for singleton components and at most one edge for two-vertex components, then sums the estimates and uses the total vertex count to absorb the small-component allowances. Empty components do not occur in the component partition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_edge_count_of_connected_induced_bounds__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hlocal : ∀ (s : Finset V),
      (K.induce (↑s : Set V)).Connected →
      (letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _;
       (K.induce (↑s : Set V)).edgeFinset.card <=
         max 1 (3 * Fintype.card s - 6))) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card <= 3 * Fintype.card V - 6) := by
  sorry
