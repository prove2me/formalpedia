-- Prove2me | Theorems.Thm_exists_maximal_element_of_finite_preorder__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1
-- name    : exists_maximal_element_of_finite_preorder__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:02:21.686376+00:00
-- url     : https://prove2.me/theorems/bc68dddc-d2b9-4455-9df5-bf61bb3b50ed
-- title:
--   An inhabited subset of a finite preorder has a maximal element
-- statement:
--   For a finite type equipped with a reflexive and transitive relation, every inhabited subset contains an element such that any related member is related back.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_element_of_finite_preorder__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1
    {α : Type} [Fintype α]
    (P : α → Prop) (r : α → α → Prop)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → r a b → r b a := by sorry
