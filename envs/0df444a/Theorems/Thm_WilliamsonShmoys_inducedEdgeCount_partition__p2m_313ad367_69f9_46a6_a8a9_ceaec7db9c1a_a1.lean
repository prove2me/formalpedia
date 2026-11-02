-- Prove2me | Theorems.Thm_WilliamsonShmoys_inducedEdgeCount_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
-- name    : WilliamsonShmoys.inducedEdgeCount_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T13:01:01.6422+00:00
-- url     : https://prove2.me/theorems/2ff00ba1-2135-4159-8a97-97b51fcb2ff7
-- title:
--   Edge conservation across an induced partition
-- statement:
--   For any finite pairwise-disjoint cover of a graph's vertices, the sum of the edge counts of the induced subgraphs on the blocks equals the graph's total edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.inducedEdgeCount_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (C : Finset (Finset V))
    (hcover : ∀ v : V, ∃ s ∈ C, v ∈ s)
    (hdisjoint : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) :
    letI : DecidableRel L.Adj := dL
    (∑ s ∈ C, (L.induce (↑s : Set V)).edgeFinset.card) = L.edgeFinset.card := by sorry
