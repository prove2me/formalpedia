-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_edge_accounting__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1
-- name    : WilliamsonShmoys.partition_edge_accounting__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:00.320311+00:00
-- url     : https://prove2.me/theorems/fc7cbe53-0857-4a4b-894a-f56a3f23db1c
-- title:
--   Edge accounting for a partition with no crossing edges
-- statement:
--   For a finite graph, a disjoint vertex partition covering all vertices counts every edge exactly once in the induced subgraphs when every edge has both endpoints in one part. Prove this by identifying each induced edge with its original edge, then using disjointness and edge locality to show these edge sets partition the original edge set. Empty graphs and isolated vertices contribute zero edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem WilliamsonShmoys.partition_edge_accounting__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (C : V → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : Finset.univ.biUnion C = Finset.univ)
    (hlocal : ∀ u v, L.Adj u v → ∃ i, u ∈ C i ∧ v ∈ C i) :
    L.edgeSet.ncard = ∑ i : V, (L.induce (fun v => v ∈ C i)).edgeSet.ncard := by sorry
