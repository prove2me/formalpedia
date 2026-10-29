-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_nonempty_subset_has_maximal__p2m_afcb74a2_92ae_4444_9657_28f7f6cf41f5_a1
-- name    : WilliamsonShmoys.finite_nonempty_subset_has_maximal__p2m_afcb74a2_92ae_4444_9657_28f7f6cf41f5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:33:58.264416+00:00
-- url     : https://prove2.me/theorems/997de6ff-2795-4635-b9b0-6618c923766b
-- title:
--   A finite nonempty subset of a finite partial order has a maximal element
-- statement:
--   In a finite partial order, every finite nonempty subset contains an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_nonempty_subset_has_maximal__p2m_afcb74a2_92ae_4444_9657_28f7f6cf41f5_a1
    {α : Type} [PartialOrder α] [Finite α] (S : Set α)
    (hS : S.Finite) (hne : S.Nonempty) :
    ∃ a, a ∈ S ∧ ∀ b, b ∈ S → a ≤ b → b = a := by sorry
