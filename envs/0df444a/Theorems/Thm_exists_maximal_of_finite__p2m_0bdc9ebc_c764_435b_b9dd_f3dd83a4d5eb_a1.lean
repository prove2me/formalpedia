-- Prove2me | Theorems.Thm_exists_maximal_of_finite__p2m_0bdc9ebc_c764_435b_b9dd_f3dd83a4d5eb_a1
-- name    : exists_maximal_of_finite__p2m_0bdc9ebc_c764_435b_b9dd_f3dd83a4d5eb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:11:46.881302+00:00
-- url     : https://prove2.me/theorems/55301982-72a2-4c81-b68d-79e3da26d5fa
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   In a finite partially ordered type, every inhabited subset contains an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_of_finite__p2m_0bdc9ebc_c764_435b_b9dd_f3dd83a4d5eb_a1
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (a₀ : α) (ha₀ : P a₀) :
    ∃ a, P a ∧ ∀ b, a ≤ b → P b → b = a := by sorry
