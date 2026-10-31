-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_of_finite_predicate__p2m_bb92451e_9d60_42f3_b7f6_3d267af0339e_a1
-- name    : WilliamsonShmoys.exists_maximal_of_finite_predicate__p2m_bb92451e_9d60_42f3_b7f6_3d267af0339e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:18:21.946798+00:00
-- url     : https://prove2.me/theorems/b5240e87-7935-46b2-954f-7b6724627c1a
-- title:
--   A nonempty finite partial order predicate has a maximal member
-- statement:
--   In a finite partial order, every nonempty predicate has a member with no strictly larger member satisfying the predicate; any qualifying member above it must equal it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_of_finite_predicate__p2m_bb92451e_9d60_42f3_b7f6_3d267af0339e_a1 {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by sorry
