-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_of_finite_predicate
-- name    : WilliamsonShmoys.exists_maximal_of_finite_predicate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:45:07.404861+00:00
-- url     : https://prove2.me/theorems/a8066646-f561-4212-84cd-fc750197032c
-- title:
--   A nonempty predicate on a finite partial order has a maximal element
-- statement:
--   In a finite partially ordered type, every nonempty predicate-defined subset contains an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_of_finite_predicate
    {α : Type} [Finite α] [PartialOrder α] (P : α → Prop)
    (hne : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, a ≤ b → P b → b = a := by
  sorry
