-- Prove2me | Theorems.Thm_finite_poset_maximal_extension__p2m_bd9d7987_6824_4383_ac2f_f887fa429ccf_a1
-- name    : finite_poset_maximal_extension__p2m_bd9d7987_6824_4383_ac2f_f887fa429ccf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:09.621256+00:00
-- url     : https://prove2.me/theorems/22b93f65-d254-488f-81b8-fc620f1fdccb
-- title:
--   Maximal extension in a finite partial order
-- statement:
--   In a finite partial order, every element satisfying a predicate has a predicate-satisfying extension that is maximal among predicate-satisfying elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem finite_poset_maximal_extension__p2m_bd9d7987_6824_4383_ac2f_f887fa429ccf_a1 {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) : ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b := by sorry
