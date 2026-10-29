-- Prove2me | Theorems.Thm_finite_poset_exists_maximal_member__p2m_2e3d33d0_6b5e_40a9_a786_4b1fab836e4e_a2
-- name    : finite_poset_exists_maximal_member__p2m_2e3d33d0_6b5e_40a9_a786_4b1fab836e4e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:13:01.268248+00:00
-- url     : https://prove2.me/theorems/3ad80762-4eb7-4a83-8cfc-9cfdebf55813
-- title:
--   A nonempty subset of a finite partial order has a maximal member
-- statement:
--   Every nonempty subset of a finite partial order has an element with no distinct larger member in that subset. Apply this to drawable graphs containing `R`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_poset_exists_maximal_member__p2m_2e3d33d0_6b5e_40a9_a786_4b1fab836e4e_a2 {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by sorry
