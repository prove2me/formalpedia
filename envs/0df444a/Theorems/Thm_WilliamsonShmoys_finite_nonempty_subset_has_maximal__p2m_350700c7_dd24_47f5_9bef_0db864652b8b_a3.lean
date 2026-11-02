-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_nonempty_subset_has_maximal__p2m_350700c7_dd24_47f5_9bef_0db864652b8b_a3
-- name    : WilliamsonShmoys.finite_nonempty_subset_has_maximal__p2m_350700c7_dd24_47f5_9bef_0db864652b8b_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:10:19.588013+00:00
-- url     : https://prove2.me/theorems/6eb3135e-ca46-4e7c-a685-0df2bbca7051
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partially ordered type has an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_nonempty_subset_has_maximal__p2m_350700c7_dd24_47f5_9bef_0db864652b8b_a3 {α : Type} [Finite α] [PartialOrder α] (S : Set α) (hS : S.Nonempty) : ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b = a := by sorry
