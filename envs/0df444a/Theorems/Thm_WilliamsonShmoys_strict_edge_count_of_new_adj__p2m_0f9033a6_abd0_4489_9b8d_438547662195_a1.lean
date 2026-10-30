-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_edge_count_of_new_adj__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1
-- name    : WilliamsonShmoys.strict_edge_count_of_new_adj__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:50:24.747433+00:00
-- url     : https://prove2.me/theorems/a43e458f-d74e-4ee0-9f88-59ad20ef06f3
-- title:
--   A new adjacency strictly increases edge count
-- statement:
--   For finite simple graphs, if every edge of K remains in L and L has an adjacency absent from K, then L has strictly more edges. The witness adjacency makes the edge-set inclusion proper; finiteness turns proper inclusion into strict cardinality growth.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

/-- Adding at least one adjacency to a finite simple graph strictly increases the cardinality of its edge set, provided no old adjacency is removed. -/

theorem WilliamsonShmoys.strict_edge_count_of_new_adj__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1 {V : Type} [Fintype V] [DecidableEq V] (K L : SimpleGraph V) (hKL : K ≤ L) (u v : V) (hL : L.Adj u v) (hK : ¬ K.Adj u v) : K.edgeSet.ncard < L.edgeSet.ncard := by sorry
