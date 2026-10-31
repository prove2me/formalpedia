-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_graph_edgeSet_extension_to_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2
-- name    : WilliamsonShmoys.simple_graph_edgeSet_extension_to_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:29:03.600327+00:00
-- url     : https://prove2.me/theorems/ff7e7d85-fbc3-441d-8708-f1cded3331d7
-- title:
--   Extend a finite simple graph to a feasible edge count
-- statement:
--   Any finite simple graph on at least three vertices whose edge count is at most 3|V|−6 has a simple supergraph on the same vertex type with exactly that many edges. This removes the finite-combinatorial completion step from the parent. A proof can add a finite subset of missing edges from the complete graph; the complete graph has enough edges at 3 vertices, 4 vertices, and every larger size under the stated bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.simple_graph_edgeSet_extension_to_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2 {V : Type} [Fintype V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hbound : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
