-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
-- name    : WilliamsonShmoys.small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:52:36.706282+00:00
-- url     : https://prove2.me/theorems/d68f4643-4bf3-4999-b07b-2e63ba7fff18
-- title:
--   Edge bound for graphs with fewer than three vertices
-- statement:
--   For a simple graph on fewer than three vertices, the edge count satisfies the target bound independently of planarity. The zero- and one-vertex cases have no edges; the two-vertex case has at most one edge while the right side is three. This follows from the generic finite simple graph edge bound by `card.choose 2` and arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hn : Fintype.card V < 3) :
    letI : DecidableRel G.Adj := Classical.decRel _
    G.edgeFinset.card ≤ 3 * Fintype.card V - 3 := by sorry
