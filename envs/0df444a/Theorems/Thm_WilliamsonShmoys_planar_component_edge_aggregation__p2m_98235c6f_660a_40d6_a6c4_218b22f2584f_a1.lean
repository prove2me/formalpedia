-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_edge_aggregation__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
-- name    : WilliamsonShmoys.planar_component_edge_aggregation__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:14.865712+00:00
-- url     : https://prove2.me/theorems/028cc941-5162-452e-8b22-e2642df436e8
-- title:
--   Aggregate graph edges over covering parts
-- statement:
--   The total edge count is at most the sum of the induced edge counts over the parts. Assign each edge to a part containing both endpoints; disjointness ensures distinct parts cannot both contain its endpoints, and `hadj` supplies existence. A proof can express this assignment as an injection between finite edge sets and the corresponding disjoint union of local edge sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_component_edge_aggregation__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (parts : Finset (Finset V))
    (hcover : ∀ v, ∃ C, C ∈ parts ∧ v ∈ C)
    (hdisjoint : ∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D)
    (hadj : ∀ u v, M.Adj u v → ∃ C, C ∈ parts ∧ u ∈ C ∧ v ∈ C) :
    M.edgeSet.ncard ≤ ∑ C ∈ parts, (M.induce (C : Set V)).edgeSet.ncard := by sorry
