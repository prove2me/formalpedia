-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_above_of_finite__p2m_1813d485_7d31_4a1e_b455_c265a709eb58_a1
-- name    : WilliamsonShmoys.exists_maximal_above_of_finite__p2m_1813d485_7d31_4a1e_b455_c265a709eb58_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:03:21.832093+00:00
-- url     : https://prove2.me/theorems/4bf14b48-65aa-4b0a-9e4a-ee92c544b11d
-- title:
--   Maximal element above a given element in a finite partial order
-- statement:
--   In a finite partial order, every element satisfying a predicate lies below a predicate-satisfying element that is maximal among predicate-satisfying elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_above_of_finite__p2m_1813d485_7d31_4a1e_b455_c265a709eb58_a1
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c ≤ b := by sorry
