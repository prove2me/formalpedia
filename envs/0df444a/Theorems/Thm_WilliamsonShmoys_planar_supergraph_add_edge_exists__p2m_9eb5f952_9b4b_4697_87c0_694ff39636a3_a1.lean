-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_add_edge_exists__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1
-- name    : WilliamsonShmoys.planar_supergraph_add_edge_exists__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:02.557153+00:00
-- url     : https://prove2.me/theorems/e3573155-f181-4a84-90e9-c4e3e1e8233c
-- title:
--   A finite graph supergraph with one additional edge exists
-- statement:
--   For finite simple graphs with nested edge sets and strictly different edge counts, there is an intermediate graph containing the smaller graph and contained in the larger graph whose edge count is exactly one larger than the smaller graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_supergraph_add_edge_exists__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1 {V : Type} [Fintype V] (M N : SimpleGraph V) (hMN : M.edgeSet ⊆ N.edgeSet) (hcard : M.edgeSet.ncard < N.edgeSet.ncard) : ∃ K : SimpleGraph V, M.edgeSet ⊆ K.edgeSet ∧ K.edgeSet ⊆ N.edgeSet ∧ K.edgeSet.ncard = M.edgeSet.ncard + 1 := by sorry
