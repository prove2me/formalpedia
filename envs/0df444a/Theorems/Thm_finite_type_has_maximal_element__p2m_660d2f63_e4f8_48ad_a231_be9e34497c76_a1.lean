-- Prove2me | Theorems.Thm_finite_type_has_maximal_element__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1
-- name    : finite_type_has_maximal_element__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:05:30.831251+00:00
-- url     : https://prove2.me/theorems/7098f3b0-a749-4dd3-913b-166c2586cde2
-- title:
--   Maximal element in a finite partial order
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_type_has_maximal_element__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1 {α : Type} [Finite α] [PartialOrder α] (S : Set α) (hS : S.Nonempty) : ∃ a, a ∈ S ∧ ∀ b, b ∈ S → a ≤ b → b ≤ a := by sorry
