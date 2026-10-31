-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_mem_set__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1
-- name    : WilliamsonShmoys.exists_maximal_mem_set__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:13:03.093249+00:00
-- url     : https://prove2.me/theorems/3bf94051-e9f7-4d5d-b224-cf18d52c9739
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element with no strictly greater element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_mem_set__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1 {α : Type} [PartialOrder α] [Finite α] (S : Set α) (hS : S.Nonempty) : ∃ a, a ∈ S ∧ ∀ b, a ≤ b → b ∈ S → b = a := by sorry
