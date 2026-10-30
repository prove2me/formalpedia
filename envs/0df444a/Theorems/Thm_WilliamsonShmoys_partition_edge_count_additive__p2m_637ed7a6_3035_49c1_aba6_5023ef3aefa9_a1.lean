-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_edge_count_additive__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
-- name    : WilliamsonShmoys.partition_edge_count_additive__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:43.274302+00:00
-- url     : https://prove2.me/theorems/ae0723d2-0b49-4ed7-b554-ecf6c2a974fd
-- title:
--   Edge counts add over an edge-closed partition
-- statement:
--   If every vertex lies in exactly one part and every edge has both endpoints in a part, the graph's edge count is the sum of the induced edge counts over the parts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.partition_edge_count_additive__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (parts : Finset (Finset V))
    (huniq : ∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W)
    (hclosed : ∀ u v : V, M.Adj u v → ∃ W ∈ parts, u ∈ W ∧ v ∈ W) :
    M.edgeSet.ncard = ∑ W ∈ parts, (M.induce (W : Set V)).edgeSet.ncard := by sorry
