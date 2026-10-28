-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_above_of_finite
-- name    : WilliamsonShmoys.exists_maximal_above_of_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:05:37.122012+00:00
-- url     : https://prove2.me/theorems/4a92a581-e483-48f3-8e01-ddc2a83ab5b4
-- title:
--   A maximal feasible element above a given element in a finite partial order
-- statement:
--   In a finite partial order, every element satisfying a predicate lies below a predicate-satisfying element that is maximal among predicate-satisfying elements above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_above_of_finite
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ m, P m ∧ a ≤ m ∧ ∀ n, m ≤ n → P n → n = m := by sorry
