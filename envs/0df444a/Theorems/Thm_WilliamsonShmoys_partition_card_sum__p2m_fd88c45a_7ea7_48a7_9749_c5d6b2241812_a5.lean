-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_card_sum__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a5
-- name    : WilliamsonShmoys_partition_card_sum__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:23:28.042932+00:00
-- url     : https://prove2.me/theorems/9dc6bd7e-b9f9-448b-a405-5231d2c1217c
-- title:
--   Cardinality sum of a finite disjoint cover
-- statement:
--   For a finite family of pairwise disjoint finite sets covering V, the sum of their cardinalities equals the cardinality of V.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_partition_card_sum__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a5 {V : Type} [Fintype V] (parts : Finset (Finset V)) (hcover : ∀ v, ∃ s ∈ parts, v ∈ s) (hdisj : ∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) : ∑ s ∈ parts, s.card = Fintype.card V := by sorry
