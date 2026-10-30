-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_poset_maximal_member__p2m_ed7e5ecf_79d4_4fb2_a080_a3796f5af948_a1
-- name    : WilliamsonShmoys.finite_poset_maximal_member__p2m_ed7e5ecf_79d4_4fb2_a080_a3796f5af948_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:20.101335+00:00
-- url     : https://prove2.me/theorems/b0563243-300f-434b-9ae4-6998c2ff4d96
-- title:
--   A nonempty subset of a finite partial order has a maximal member
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element with no strictly larger member in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_poset_maximal_member__p2m_ed7e5ecf_79d4_4fb2_a080_a3796f5af948_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (s : Set α) (hs : s.Nonempty) :
    ∃ a : α, s a ∧ ∀ b : α, s b → a ≤ b → b ≤ a := by sorry
