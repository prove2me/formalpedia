-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_exists_maximal
-- name    : WilliamsonShmoys.finite_exists_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:20:50.886487+00:00
-- url     : https://prove2.me/theorems/2e98e85b-6685-4b22-8912-d1ba9cfccb6d
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   In a finite partially ordered type, every nonempty subset contains an element with no distinct greater element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_exists_maximal {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by sorry
