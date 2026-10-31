-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_graph_small_edge_bound__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
-- name    : WilliamsonShmoys.simple_graph_small_edge_bound__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:17:08.475633+00:00
-- url     : https://prove2.me/theorems/1a258cf3-0f1f-4419-b735-6517bde3437a
-- title:
--   Simple graphs on fewer than three vertices have at most one edge
-- statement:
--   Every finite simple graph on fewer than three vertices has at most one edge. This handles the target’s small-cardinality branch; its maximum is at least one even when the vertex count is zero.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.simple_graph_small_edge_bound__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hsmall : Fintype.card V < 3) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card ≤ 1) := by sorry
