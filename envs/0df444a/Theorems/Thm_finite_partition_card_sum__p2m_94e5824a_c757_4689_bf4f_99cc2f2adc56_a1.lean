-- Prove2me | Theorems.Thm_finite_partition_card_sum__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1
-- name    : finite_partition_card_sum__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:29.735173+00:00
-- url     : https://prove2.me/theorems/e5cdccd9-18d7-4276-8c04-d72aa56b3fc7
-- title:
--   Cardinality sum for a finite partition
-- statement:
--   For a finite family of finite sets in which every vertex belongs to exactly one member, the sum of the member cardinalities equals the cardinality of the vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_partition_card_sum__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1
    {V : Type} [Fintype V] (parts : Finset (Finset V))
    (huniq : ∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W) :
    Fintype.card V = ∑ W ∈ parts, W.card := by sorry
