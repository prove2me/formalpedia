-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_above_finite_partial_order__p2m_867a30c3_e0cd_4780_a6e7_8570584f57fd_a1
-- name    : WilliamsonShmoys.exists_maximal_above_finite_partial_order__p2m_867a30c3_e0cd_4780_a6e7_8570584f57fd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:52.250772+00:00
-- url     : https://prove2.me/theorems/1ed7e29f-6eba-432c-bedd-532371640d75
-- title:
--   Maximal element above a given element in a finite partial order
-- statement:
--   In a finite partial order, any element satisfying a property lies below a property-satisfying element that is maximal among property-satisfying elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_above_finite_partial_order__p2m_867a30c3_e0cd_4780_a6e7_8570584f57fd_a1 {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) : ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c ≤ b := by sorry
