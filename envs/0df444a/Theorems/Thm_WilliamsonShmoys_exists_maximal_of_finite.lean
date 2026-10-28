-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_of_finite
-- name    : WilliamsonShmoys.exists_maximal_of_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:44:16.563328+00:00
-- url     : https://prove2.me/theorems/12b25b0d-e90b-4f5d-8d46-5d3f93846d08
-- title:
--   Maximal element above a point in a finite partial order
-- statement:
--   In a finite partial order, if a predicate holds at a, there is a predicate-satisfying element above a that has no strictly larger predicate-satisfying element.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_of_finite {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) : ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b := by sorry
