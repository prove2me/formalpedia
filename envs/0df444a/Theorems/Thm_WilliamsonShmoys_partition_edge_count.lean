-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_edge_count
-- name    : WilliamsonShmoys.partition_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:44:07.894876+00:00
-- url     : https://prove2.me/theorems/1f93653c-1f8e-4d78-a73a-09d2ea17c769
-- title:
--   Edge counts add across an edge-respecting partition
-- statement:
--   For any pairwise-disjoint finite vertex partition covering all vertices, if every adjacent pair belongs to a common block, the graph’s edge count equals the sum of the induced edge counts of its blocks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.partition_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (parts : Finset (Finset V))
    (hdisjoint : ∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D)
    (hcover : parts.biUnion id = Finset.univ)
    (hadj : ∀ u v, G.Adj u v → ∃ C ∈ parts, u ∈ C ∧ v ∈ C) :
    G.edgeSet.ncard = ∑ C ∈ parts, (G.induce (fun v => v ∈ C)).edgeSet.ncard := by sorry
