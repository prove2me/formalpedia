-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_subgraph_count_9064c577
-- name    : WilliamsonShmoys.edge_bound_of_subgraph_count_9064c577
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:06:37.694465+00:00
-- url     : https://prove2.me/theorems/721f55b6-7252-404a-a0e8-2acc1ff209fb
-- title:
--   Edge bound inherited from a counted supergraph
-- statement:
--   If a finite graph’s edge set is contained in another graph’s edge set, and the larger graph has exactly 3|V|−6 edges, then the smaller graph has at most that many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_of_subgraph_count_9064c577
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V)
    (hSub : K.edgeSet ⊆ H.edgeSet)
    (hCount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
