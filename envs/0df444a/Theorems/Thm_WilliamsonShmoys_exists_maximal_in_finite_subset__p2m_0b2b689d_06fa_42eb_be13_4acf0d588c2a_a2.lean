-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_in_finite_subset__p2m_0b2b689d_06fa_42eb_be13_4acf0d588c2a_a2
-- name    : WilliamsonShmoys.exists_maximal_in_finite_subset__p2m_0b2b689d_06fa_42eb_be13_4acf0d588c2a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:44:35.309137+00:00
-- url     : https://prove2.me/theorems/ca6bcb84-97fa-4c29-8f2c-0635aa6fb7b7
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partially ordered type has an element with no strictly larger element in that subset. The witness `a` certifies that the subset is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_in_finite_subset__p2m_0b2b689d_06fa_42eb_be13_4acf0d588c2a_a2
    {α : Type} [Finite α] [PartialOrder α]
    (s : Set α) (a : α) (ha : a ∈ s) :
    ∃ m, m ∈ s ∧ ∀ x, x ∈ s → m ≤ x → x ≤ m := by sorry
