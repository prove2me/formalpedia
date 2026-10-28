-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_partialOrder_maximal_extension
-- name    : WilliamsonShmoys.finite_partialOrder_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:35:58.961978+00:00
-- url     : https://prove2.me/theorems/15521c6d-6e66-4ddd-a2d7-e2e3f06db5d9
-- title:
--   Maximal extension in a finite partial order
-- statement:
--   In a finite partially ordered type, every element satisfying a property has a maximal extension among elements satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_partialOrder_maximal_extension
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧
      ∀ c : α, P c → b ≤ c → b = c := by sorry
