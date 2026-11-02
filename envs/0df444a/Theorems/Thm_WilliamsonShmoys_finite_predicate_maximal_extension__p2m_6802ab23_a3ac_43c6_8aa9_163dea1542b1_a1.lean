-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal_extension__p2m_6802ab23_a3ac_43c6_8aa9_163dea1542b1_a1
-- name    : WilliamsonShmoys.finite_predicate_maximal_extension__p2m_6802ab23_a3ac_43c6_8aa9_163dea1542b1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:55:25.188335+00:00
-- url     : https://prove2.me/theorems/af80b6aa-ec4a-4dc9-b02c-284c5cc8a05f
-- title:
--   Maximal element of a finite predicate above a witness
-- statement:
--   In a finite partial order, any element satisfying a predicate lies below a predicate-satisfying element that is maximal among predicate-satisfying elements above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_predicate_maximal_extension__p2m_6802ab23_a3ac_43c6_8aa9_163dea1542b1_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b, a ≤ b ∧ P b ∧ ∀ c, b ≤ c → P c → c = b := by sorry
