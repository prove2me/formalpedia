-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension
-- name    : WilliamsonShmoys.finite_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:08:06.06152+00:00
-- url     : https://prove2.me/theorems/96573f0b-f668-4913-88c9-3e285e1b3e75
-- title:
--   A finite partially ordered type has a maximal eligible extension
-- statement:
--   In a finite partially ordered type, every element satisfying P has an extension that satisfies P and is maximal among all P-elements above it. This removes the graph-specific maximality argument from the parent; it can be proved by a finite ascent through eligible elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (a₀ : α) (ha₀ : P a₀) :
    ∃ a : α, a₀ ≤ a ∧ P a ∧ ∀ b : α, a ≤ b → P b → b ≤ a := by sorry
