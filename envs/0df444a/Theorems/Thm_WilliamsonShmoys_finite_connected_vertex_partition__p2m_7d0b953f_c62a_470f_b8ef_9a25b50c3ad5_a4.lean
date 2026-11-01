-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4
-- name    : WilliamsonShmoys.finite_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:50:49.091258+00:00
-- url     : https://prove2.me/theorems/3476ae87-a4f6-40d5-bdc0-066b706311ab
-- title:
--   Finite partition into connected induced subgraphs
-- statement:
--   Every finite graph has a finite family of nonempty vertex sets that cover the vertices, are pairwise disjoint, induce connected subgraphs, and contain both endpoints of every edge in some part. Grouping vertices by graph reachability provides an independent proof route; the claim also covers the empty vertex type, where the family can be empty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ s ∈ parts, s.Nonempty ∧ (K.induce (↑s : Set V)).Connected) ∧
      (∀ v, ∃ s ∈ parts, v ∈ s) ∧
      (∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) ∧
      (∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s) := by sorry
