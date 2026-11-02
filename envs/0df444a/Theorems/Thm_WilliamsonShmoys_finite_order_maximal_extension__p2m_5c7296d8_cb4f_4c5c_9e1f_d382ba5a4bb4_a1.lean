-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_order_maximal_extension__p2m_5c7296d8_cb4f_4c5c_9e1f_d382ba5a4bb4_a1
-- name    : WilliamsonShmoys.finite_order_maximal_extension__p2m_5c7296d8_cb4f_4c5c_9e1f_d382ba5a4bb4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:18:59.508786+00:00
-- url     : https://prove2.me/theorems/c28376cb-179b-4b9b-b764-4c354b50499e
-- title:
--   Maximal extension in a finite partial order
-- statement:
--   In a finite partially ordered type, every element satisfying a predicate lies below a predicate-satisfying maximal element. The predicate need not be upward closed; maximality is among elements satisfying the predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_order_maximal_extension__p2m_5c7296d8_cb4f_4c5c_9e1f_d382ba5a4bb4_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (x : α) (hx : P x) :
    ∃ y : α, x ≤ y ∧ P y ∧ ∀ z : α, y ≤ z → P z → z = y := by sorry
