-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_above_in_finite_partial_order
-- name    : WilliamsonShmoys.exists_maximal_above_in_finite_partial_order
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:52:29.557536+00:00
-- url     : https://prove2.me/theorems/62a14145-541c-4cb2-8f55-d95e6860b39d
-- title:
--   Maximal element above a member in a finite partial order
-- statement:
--   In a finite partial order, every element satisfying a predicate lies below a maximal element satisfying that predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_above_in_finite_partial_order {α : Type} [Finite α] [PartialOrder α] (x : α) (P : α → Prop) (hx : P x) : ∃ y : α, x ≤ y ∧ P y ∧ ∀ z : α, y ≤ z → P z → y = z := by sorry
