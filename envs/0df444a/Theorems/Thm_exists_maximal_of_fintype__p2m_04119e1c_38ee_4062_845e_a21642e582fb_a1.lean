-- Prove2me | Theorems.Thm_exists_maximal_of_fintype__p2m_04119e1c_38ee_4062_845e_a21642e582fb_a1
-- name    : exists_maximal_of_fintype__p2m_04119e1c_38ee_4062_845e_a21642e582fb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:01:07.66314+00:00
-- url     : https://prove2.me/theorems/3c93ff63-09f8-4eb2-b054-3130133fe7d9
-- title:
--   Maximal element of a nonempty subset of a finite partial order
-- statement:
--   Every nonempty subset of a finite partial order contains an element with no strictly greater element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem exists_maximal_of_fintype__p2m_04119e1c_38ee_4062_845e_a21642e582fb_a1 {α : Type} [Fintype α] [PartialOrder α] (S : α → Prop) (hS : ∃ a, S a) : ∃ a, S a ∧ ∀ b, S b → a ≤ b → b ≤ a := by sorry
