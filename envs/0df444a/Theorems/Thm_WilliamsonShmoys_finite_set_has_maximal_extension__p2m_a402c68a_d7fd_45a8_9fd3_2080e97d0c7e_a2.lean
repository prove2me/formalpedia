-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_set_has_maximal_extension__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2
-- name    : WilliamsonShmoys.finite_set_has_maximal_extension__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:17:53.355193+00:00
-- url     : https://prove2.me/theorems/e398df3f-4214-469f-8848-07fc5fa6d380
-- title:
--   Maximal element above a member of a finite preorder set
-- statement:
--   In a finite subset of a preorder, every member lies below an element of the subset that is maximal up to preorder equivalence.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_set_has_maximal_extension__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2 {α : Type} [Preorder α] (S : Set α) (hS : S.Finite) (a : α) (ha : a ∈ S) : ∃ b, b ∈ S ∧ a ≤ b ∧ ∀ c, b ≤ c → c ∈ S → c ≤ b := by sorry
