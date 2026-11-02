-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_member__p2m_23f134b1_374c_4250_9a94_0278c2487544_a1
-- name    : WilliamsonShmoys.finite_maximal_member__p2m_23f134b1_374c_4250_9a94_0278c2487544_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:15:58.477171+00:00
-- url     : https://prove2.me/theorems/939c1f6c-edc0-4065-8329-81d1d9a86060
-- title:
--   A finite partial order has a maximal extension
-- statement:
--   In a finite partial order, any element satisfying P lies below a P-element that is maximal among all P-elements above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_member__p2m_23f134b1_374c_4250_9a94_0278c2487544_a1 {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (s : α) (hP : P s) : ∃ m : α, s ≤ m ∧ P m ∧ ∀ b : α, m ≤ b → P b → b = m := by sorry
