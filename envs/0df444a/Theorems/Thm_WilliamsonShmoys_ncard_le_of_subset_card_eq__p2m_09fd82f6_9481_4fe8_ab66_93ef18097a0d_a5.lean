-- Prove2me | Theorems.Thm_WilliamsonShmoys_ncard_le_of_subset_card_eq__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
-- name    : WilliamsonShmoys.ncard_le_of_subset_card_eq__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:15:31.982248+00:00
-- url     : https://prove2.me/theorems/b870078f-f6c7-457f-be72-a62590c6552b
-- title:
--   Cardinality bound from finite-set inclusion
-- statement:
--   For finite sets `s ⊆ t`, if `t` has cardinality `k`, then `s` has cardinality at most `k`. This separates the edge-set counting step from the topological completion step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.ncard_le_of_subset_card_eq__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
    {α : Type} [Fintype α]
    (s t : Set α) (k : ℕ)
    (hsub : s ⊆ t)
    (hcard : t.ncard = k) :
    s.ncard ≤ k := by sorry
