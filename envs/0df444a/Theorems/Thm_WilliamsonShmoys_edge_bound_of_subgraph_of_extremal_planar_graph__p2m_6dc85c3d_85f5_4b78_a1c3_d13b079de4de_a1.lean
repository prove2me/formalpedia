-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_subgraph_of_extremal_planar_graph__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
-- name    : WilliamsonShmoys.edge_bound_of_subgraph_of_extremal_planar_graph__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:29:05.148441+00:00
-- url     : https://prove2.me/theorems/f5bf08f0-0aeb-4ea0-b608-6f2c3628e2ce
-- title:
--   Edge bound inherited by a subgraph
-- statement:
--   If one finite simple graph is a subgraph of another graph on the same vertices, then an exact edge-count formula for the larger graph implies the corresponding upper bound for the smaller graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_of_subgraph_of_extremal_planar_graph__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) (hMN : M ≤ N)
    (hN : (letI : DecidableRel N.Adj := Classical.decRel N.Adj
           N.edgeFinset.card + 6 = 3 * Fintype.card V)) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     letI : DecidableRel N.Adj := Classical.decRel N.Adj
     M.edgeFinset.card + 6 <= 3 * Fintype.card V) := by sorry
