-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_connected_induced_subgraphs
-- name    : WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:58:44.740925+00:00
-- url     : https://prove2.me/theorems/c3a2b79a-bad9-4d3a-b29f-3fe24b1acb7a
-- title:
--   Combine connected induced-subgraph bounds
-- statement:
--   If every connected induced subgraph on at least three vertices satisfies the planar edge bound, then the whole finite simple graph satisfies it whenever the total vertex count is at least three. This removes the disconnected-component bookkeeping from the parent. Prove it by partitioning the vertices into connected components, applying the hypothesis to components of size at least three, and using simplicity to bound edges in singleton and two-vertex components; their deficits, together with the total-size condition, give a total deficit of at least six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hS : ∀ S : Finset V, 3 ≤ S.card →
      (K.induce (↑S : Set V)).Connected →
      (K.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
