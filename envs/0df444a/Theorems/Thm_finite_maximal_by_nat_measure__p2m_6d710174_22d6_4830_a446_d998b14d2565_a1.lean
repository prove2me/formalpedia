-- Prove2me | Theorems.Thm_finite_maximal_by_nat_measure__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
-- name    : finite_maximal_by_nat_measure__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:40:57.157803+00:00
-- url     : https://prove2.me/theorems/e8fab6d5-fcb4-413a-8bc1-08b5f944e4af
-- title:
--   Finite maximal element by a natural-valued measure
-- statement:
--   On a finite type, if a predicate is nonempty and a natural-valued measure strictly increases along every related pair of distinct predicate elements, then some predicate element has no distinct related successor.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_maximal_by_nat_measure__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
    {α : Type} [Fintype α] (P : α → Prop) (R : α → α → Prop) (measure : α → Nat)
    (hP : ∃ a, P a)
    (hstrict : ∀ a b, P a → P b → R a b → a ≠ b → measure a < measure b) :
    ∃ a, P a ∧ ∀ b, P b → R a b → a = b := by sorry
