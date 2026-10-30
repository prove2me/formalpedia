-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_partial_order_maximal_extension__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1
-- name    : WilliamsonShmoys.finite_partial_order_maximal_extension__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:49:58.918492+00:00
-- url     : https://prove2.me/theorems/a2f3c42e-342a-47c0-8c88-3be35f548af6
-- title:
--   A finite partial order has maximal extensions within a predicate
-- statement:
--   In a finite partially ordered type, any element satisfying a predicate has an extension satisfying that predicate which is maximal among such extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_partial_order_maximal_extension__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c ≤ b := by sorry
