-- Prove2me | Theorems.Thm_exists_maximal_of_finite_family__p2m_76ca258b_4f2e_4801_9d46_2c2421541685_a1
-- name    : exists_maximal_of_finite_family__p2m_76ca258b_4f2e_4801_9d46_2c2421541685_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:36:34.414708+00:00
-- url     : https://prove2.me/theorems/f9218f15-a699-43da-8b15-00bc3a5ae167
-- title:
--   Maximal member of a nonempty finite partially ordered family
-- statement:
--   Every nonempty family in a finite partially ordered type contains a member with no strictly larger member in that family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem exists_maximal_of_finite_family__p2m_76ca258b_4f2e_4801_9d46_2c2421541685_a1
    {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by sorry
