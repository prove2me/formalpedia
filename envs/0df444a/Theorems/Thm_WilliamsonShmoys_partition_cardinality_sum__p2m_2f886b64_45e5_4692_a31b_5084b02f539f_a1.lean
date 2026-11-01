-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_cardinality_sum__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
-- name    : WilliamsonShmoys.partition_cardinality_sum__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:13:27.809623+00:00
-- url     : https://prove2.me/theorems/271a7c0d-63c8-473a-b0db-ae1f1287f5cd
-- title:
--   Cardinalities of a disjoint cover sum to the whole
-- statement:
--   For a finite disjoint cover, summing the cardinalities of the subsets equals the cardinality of the covered type. Empty members, if present, contribute zero.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.partition_cardinality_sum__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1 {V : Type} [Fintype V] (parts : Finset (Finset V)) (hcover : ∀ v, ∃ C, C ∈ parts ∧ v ∈ C) (hdisjoint : ∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D) : (∑ C ∈ parts, Fintype.card {x : V // x ∈ C}) = Fintype.card V := by sorry
