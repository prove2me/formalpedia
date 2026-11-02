-- Prove2me | Theorems.Thm_finite_maximal_of_strict_measure__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a1
-- name    : finite_maximal_of_strict_measure__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:48.675802+00:00
-- url     : https://prove2.me/theorems/279f03e2-3082-4242-9232-6ad7770b8c8b
-- title:
--   Finite maximal element from a strictly increasing measure
-- statement:
--   For a finite partially ordered type, if a natural-valued measure strictly increases under every proper extension, every nonempty predicate has an element with no proper extension satisfying that predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_maximal_of_strict_measure__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a1 {α : Type} [Fintype α] [PartialOrder α] (Q : α → Prop) (measure : α → Nat) (hstrict : ∀ a b, a ≤ b → a ≠ b → measure a < measure b) (hne : ∃ a, Q a) : ∃ a, Q a ∧ ∀ b, Q b → a ≤ b → b = a := by sorry
