-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_inclusion_maximal_graph__p2m_78ba916f_f700_41ef_a045_eff3bbec17a0_a2
-- name    : WilliamsonShmoys.exists_edge_inclusion_maximal_graph__p2m_78ba916f_f700_41ef_a045_eff3bbec17a0_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:45:22.567759+00:00
-- url     : https://prove2.me/theorems/0c9be13c-5f74-4c69-8dd8-5d16899823da
-- title:
--   Finite maximality for a predicate on simple graphs
-- statement:
--   On a finite linearly ordered vertex type, every graph satisfying a predicate is contained in a graph that is maximal under edge inclusion among graphs satisfying that predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_edge_inclusion_maximal_graph__p2m_78ba916f_f700_41ef_a045_eff3bbec17a0_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) : ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ P H ∧ ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → P K → K.edgeSet = H.edgeSet := by sorry
