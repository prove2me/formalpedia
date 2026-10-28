-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_partial_order_has_maximal_extension
-- name    : WilliamsonShmoys.finite_partial_order_has_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:55:47.807365+00:00
-- url     : https://prove2.me/theorems/c1ad0202-cd0c-4f85-9fa8-2a027fd49d04
-- title:
--   Maximal predicate-satisfying extension in a finite partial order
-- statement:
--   In a finite partially ordered type, every element satisfying a predicate has a predicate-satisfying extension that is maximal among such extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_partial_order_has_maximal_extension
    {α : Type} [Fintype α] [PartialOrder α]
    (R : α → Prop)
    (a : α)
    (ha : R a) :
    ∃ b : α, a ≤ b ∧ R b ∧
      ∀ c : α, b ≤ c → R c → c = b := by
  sorry
