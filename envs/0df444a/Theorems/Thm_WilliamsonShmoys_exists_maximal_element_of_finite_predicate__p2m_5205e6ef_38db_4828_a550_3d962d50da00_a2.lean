-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_element_of_finite_predicate__p2m_5205e6ef_38db_4828_a550_3d962d50da00_a2
-- name    : WilliamsonShmoys.exists_maximal_element_of_finite_predicate__p2m_5205e6ef_38db_4828_a550_3d962d50da00_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:27:15.096536+00:00
-- url     : https://prove2.me/theorems/ffbf8c1b-3075-46f2-80c4-b82568530bf9
-- title:
--   Maximal element in a finite partially ordered predicate
-- statement:
--   Every nonempty predicate on a finite partially ordered type has an element with no strictly larger predicate element.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_element_of_finite_predicate__p2m_5205e6ef_38db_4828_a550_3d962d50da00_a2
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by sorry
