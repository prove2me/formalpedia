-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_partial_order_has_maximal_above__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2
-- name    : WilliamsonShmoys.finite_partial_order_has_maximal_above__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:55:38.789777+00:00
-- url     : https://prove2.me/theorems/d26bda2e-7deb-4ec6-90b1-49d53d9db466
-- title:
--   Maximal element above a predicate witness in a finite partial order
-- statement:
--   In a finite partially ordered type, any element satisfying a predicate lies below a predicate-satisfying element that is maximal among predicate-satisfying elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_partial_order_has_maximal_above__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2 {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) : ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, P c → b ≤ c → c ≤ b := by sorry
