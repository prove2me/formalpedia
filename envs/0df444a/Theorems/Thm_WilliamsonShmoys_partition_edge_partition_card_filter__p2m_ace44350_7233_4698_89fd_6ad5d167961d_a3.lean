-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_edge_partition_card_filter__p2m_ace44350_7233_4698_89fd_6ad5d167961d_a3
-- name    : WilliamsonShmoys.partition_edge_partition_card_filter__p2m_ace44350_7233_4698_89fd_6ad5d167961d_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:33:44.599617+00:00
-- url     : https://prove2.me/theorems/b58fa787-3001-4cbd-800f-e7eedb447626
-- title:
--   Count edges by their unique containing part
-- statement:
--   The total number of edges equals the sum, over the parts, of the number of edges whose endpoints lie in that part. Coverage gives each edge a containing part; pairwise disjointness makes that part unique.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.partition_edge_partition_card_filter__p2m_ace44350_7233_4698_89fd_6ad5d167961d_a3 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (parts : Finset (Finset V)) (hdisj : ∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) (hcontain : ∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s) : (letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card = ∑ s ∈ parts, (K.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card) := by sorry
