-- Prove2me | Theorems.Thm_exists_maximal_element_of_finite_set__p2m_5ad4dfa2_7b03_4649_bf47_2550ad7ee6b8_a1
-- name    : exists_maximal_element_of_finite_set__p2m_5ad4dfa2_7b03_4649_bf47_2550ad7ee6b8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:21.173098+00:00
-- url     : https://prove2.me/theorems/1ca86e04-6895-4fd9-8578-3ceab2d9eba6
-- title:
--   A finite nonempty set in a preorder has a maximal element
-- statement:
--   Every finite nonempty subset of a preorder contains an element with no strictly larger member of that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_element_of_finite_set__p2m_5ad4dfa2_7b03_4649_bf47_2550ad7ee6b8_a1
    {α : Type} [Finite α] [Preorder α]
    (S : Set α) (hS : S.Finite) (hSne : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b ≤ a := by sorry
