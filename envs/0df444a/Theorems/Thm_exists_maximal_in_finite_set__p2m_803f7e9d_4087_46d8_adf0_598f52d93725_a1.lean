-- Prove2me | Theorems.Thm_exists_maximal_in_finite_set__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1
-- name    : exists_maximal_in_finite_set__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:09.442435+00:00
-- url     : https://prove2.me/theorems/5c1df917-6ada-452f-a67f-f55e4def0124
-- title:
--   A nonempty subset of a finite preorder has a maximal member
-- statement:
--   Every nonempty subset of a finite preorder contains an element such that every larger element in the subset is also below it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem exists_maximal_in_finite_set__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1
    {α : Type} [Finite α] [Preorder α]
    (s : Set α) (hne : s.Nonempty) :
    ∃ a, a ∈ s ∧ ∀ b, b ∈ s → a ≤ b → b ≤ a := by sorry
