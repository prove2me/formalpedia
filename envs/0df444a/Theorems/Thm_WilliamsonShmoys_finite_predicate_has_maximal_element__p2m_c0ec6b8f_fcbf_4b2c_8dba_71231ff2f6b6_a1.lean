-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_predicate_has_maximal_element__p2m_c0ec6b8f_fcbf_4b2c_8dba_71231ff2f6b6_a1
-- name    : WilliamsonShmoys.finite_predicate_has_maximal_element__p2m_c0ec6b8f_fcbf_4b2c_8dba_71231ff2f6b6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:49:34.02767+00:00
-- url     : https://prove2.me/theorems/70bed621-d783-441d-a804-6b3324c086df
-- title:
--   A nonempty predicate on a finite partial order has a maximal element
-- statement:
--   Every nonempty predicate on a finite partially ordered type contains an element that has no strictly larger element satisfying the predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

universe u

theorem WilliamsonShmoys.finite_predicate_has_maximal_element__p2m_c0ec6b8f_fcbf_4b2c_8dba_71231ff2f6b6_a1
    {α : Type u} [Fintype α] [PartialOrder α]
    (P : α → Prop) (hP : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x ≤ y → y ≤ x := by sorry
