-- Prove2me | Theorems.Thm_finite_partial_order_exists_maximal
-- name    : finite_partial_order_exists_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:41:21.686058+00:00
-- url     : https://prove2.me/theorems/e0f7d583-c363-4b8f-836a-5cb4e9958785
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partial order contains an element with no strictly greater member in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_partial_order_exists_maximal {α : Type} [Finite α] [PartialOrder α] (s : Set α) (hne : s.Nonempty) : ∃ a, a ∈ s ∧ ∀ b, b ∈ s → a ≤ b → b = a := by sorry
