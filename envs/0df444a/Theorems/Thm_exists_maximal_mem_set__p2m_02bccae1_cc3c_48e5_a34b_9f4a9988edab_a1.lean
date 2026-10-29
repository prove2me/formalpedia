-- Prove2me | Theorems.Thm_exists_maximal_mem_set__p2m_02bccae1_cc3c_48e5_a34b_9f4a9988edab_a1
-- name    : exists_maximal_mem_set__p2m_02bccae1_cc3c_48e5_a34b_9f4a9988edab_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:45:30.815108+00:00
-- url     : https://prove2.me/theorems/2a9c7f88-bc19-40ef-be14-6ba573b95df5
-- title:
--   Maximal element in a nonempty subset of a finite partial order
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element with no strictly larger member in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem exists_maximal_mem_set__p2m_02bccae1_cc3c_48e5_a34b_9f4a9988edab_a1 {α : Type} [Finite α] [PartialOrder α] (s : Set α) (hne : s.Nonempty) : ∃ a, a ∈ s ∧ ∀ b, a ≤ b → b ∈ s → b ≤ a := by sorry
