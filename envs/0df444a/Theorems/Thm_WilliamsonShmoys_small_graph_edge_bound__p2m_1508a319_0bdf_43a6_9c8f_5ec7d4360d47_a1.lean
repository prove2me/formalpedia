-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a1
-- name    : WilliamsonShmoys.small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:36:18.739041+00:00
-- url     : https://prove2.me/theorems/b07a9a50-ccf2-439f-8650-40341b495447
-- title:
--   Edge bound for graphs with fewer than three vertices
-- statement:
--   Every simple graph with fewer than three vertices satisfies the requested Nat-subtraction bound, independently of planarity: the 0- and 1-vertex cases have no edges, and the 2-vertex case has at most one edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hn : Fintype.card V < 3) :
    letI : DecidableRel G.Adj := Classical.decRel _
    G.edgeFinset.card ≤ 3 * Fintype.card V - 3 := by sorry
