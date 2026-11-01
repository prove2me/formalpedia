-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4
-- name    : WilliamsonShmoys.edge_bound_of_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:50:56.299607+00:00
-- url     : https://prove2.me/theorems/6c5365e9-a8ca-483d-a274-7738f7675557
-- title:
--   Aggregate local edge bounds across a connected partition
-- statement:
--   Given the stated partition and local bounds on every connected induced subgraph, the graph satisfies the global edge bound when it has at least three vertices. Partition edges by their unique part, use zero edges for singleton parts, at most one for two-vertex parts, and the local estimate for larger parts, then sum and absorb the small-part allowances. This isolates the aggregation argument from the construction of the partition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_of_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hlocal : ∀ (s : Finset V),
      (K.induce (↑s : Set V)).Connected →
      (letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _;
       (K.induce (↑s : Set V)).edgeFinset.card <=
         max 1 (3 * Fintype.card s - 6)))
    (parts : Finset (Finset V))
    (hparts :
      (∀ s ∈ parts, s.Nonempty ∧ (K.induce (↑s : Set V)).Connected) ∧
      (∀ v, ∃ s ∈ parts, v ∈ s) ∧
      (∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) ∧
      (∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s)) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card <= 3 * Fintype.card V - 6) := by sorry
