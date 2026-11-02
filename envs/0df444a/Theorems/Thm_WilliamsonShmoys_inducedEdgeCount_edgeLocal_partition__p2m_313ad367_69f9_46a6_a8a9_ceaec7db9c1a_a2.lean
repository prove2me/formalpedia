-- Prove2me | Theorems.Thm_WilliamsonShmoys_inducedEdgeCount_edgeLocal_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
-- name    : WilliamsonShmoys.inducedEdgeCount_edgeLocal_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:47:59.262405+00:00
-- url     : https://prove2.me/theorems/8acc3f5b-9293-4628-a0e4-df0d21833f16
-- title:
--   Edge conservation for an edge-local partition
-- statement:
--   For a finite graph, if a disjoint cover places both endpoints of every edge in a common block, then the induced subgraphs’ edge counts sum to the graph’s edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.inducedEdgeCount_edgeLocal_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (C : Finset (Finset V))
    (hcover : ∀ v : V, ∃ s ∈ C, v ∈ s)
    (hdisjoint : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hedgeLocal : ∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    letI : DecidableRel L.Adj := dL
    (∑ s ∈ C, (L.induce (↑s : Set V)).edgeFinset.card) = L.edgeFinset.card := by sorry
