-- Prove2me | Theorems.Thm_WilliamsonShmoys_sum_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2
-- name    : WilliamsonShmoys.sum_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:36.919645+00:00
-- url     : https://prove2.me/theorems/c61a9b30-fae7-44f5-ae1c-615590b0ab97
-- title:
--   Aggregate component deficits
-- statement:
--   Aggregate the local inequalities using the vertex and edge count identities. If any part has size at least three, its deficit is six. Otherwise, each nonempty part contributes a deficit of three, and at least two parts are needed because the total vertex count is at least three. Thus the total deficit is at least six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.sum_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (parts : Finset (Finset V)) (hCardSum : (∑ s ∈ parts, Fintype.card {v // v ∈ s}) = Fintype.card V) (hEdgeSum : (∑ s ∈ parts, (H.induce (↑s : Set V)).edgeSet.ncard) = H.edgeSet.ncard) (hLocal : ∀ s ∈ parts, 1 ≤ Fintype.card {v // v ∈ s} ∧ (H.induce (↑s : Set V)).Connected ∧ (H.induce (↑s : Set V)).edgeSet.ncard + (if 3 ≤ Fintype.card {v // v ∈ s} then 6 else 3) ≤ 3 * Fintype.card {v // v ∈ s}) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
