-- Prove2me | Theorems.Thm_exists_maximal_of_finite_partialOrder__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2
-- name    : exists_maximal_of_finite_partialOrder__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:33.633992+00:00
-- url     : https://prove2.me/theorems/00f62bfc-ff45-407b-8a41-05c470de69ea
-- title:
--   Maximal member of a nonempty subset of a finite partial order
-- statement:
--   Every nonempty subset of a finite partial order contains an element with no strictly greater element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_of_finite_partialOrder__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2 {α : Type} [PartialOrder α] [Finite α] (P : α → Prop) (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, a ≤ b → b ≠ a → ¬ P b := by sorry
