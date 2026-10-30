-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_finite_order__p2m_fe6ffdb7_db07_4cee_9965_0cee09c3b00f_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_finite_order__p2m_fe6ffdb7_db07_4cee_9965_0cee09c3b00f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:56:21.602229+00:00
-- url     : https://prove2.me/theorems/f7fabca3-bdf4-4c1d-a2e3-026869c93938
-- title:
--   Maximal extension in a finite partial order
-- statement:
--   In a finite partially ordered type, every element satisfying a predicate has a maximal predicate-satisfying extension above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_extension_finite_order__p2m_fe6ffdb7_db07_4cee_9965_0cee09c3b00f_a1 {α : Type} [Fintype α] [PartialOrder α] (Q : α → Prop) (x : α) (hx : Q x) : ∃ y : α, x ≤ y ∧ Q y ∧ ∀ z : α, y ≤ z → Q z → z ≤ y := by sorry
