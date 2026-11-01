-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_edge_partition_card__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1
-- name    : WilliamsonShmoys.partition_edge_partition_card__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:08.795384+00:00
-- url     : https://prove2.me/theorems/ace44350-7233-4698-89fd-6ad5d167961d
-- title:
--   Count edges across a disjoint edge-covering family
-- statement:
--   If the parts are pairwise disjoint and every edge has both endpoints in some part, the total edge count equals the sum of the induced edge counts. Each global edge belongs to exactly one part: existence follows from edge containment, and uniqueness follows from disjointness and the distinct endpoints of a simple-graph edge. A proof can establish a bijection between global edges and the disjoint union of the parts' induced edge sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.partition_edge_partition_card__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (parts : Finset (Finset V)) (hdisj : ∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) (hcontain : ∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s) : (letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card = ∑ s ∈ parts, (K.induce (↑s : Set V)).edgeFinset.card) := by sorry
