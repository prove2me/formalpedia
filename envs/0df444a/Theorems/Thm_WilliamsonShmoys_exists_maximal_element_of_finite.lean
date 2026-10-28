-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_element_of_finite
-- name    : WilliamsonShmoys.exists_maximal_element_of_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:39:33.737502+00:00
-- url     : https://prove2.me/theorems/f50b9c74-231e-4e78-9009-65a876b6e3ff
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element that cannot be strictly increased within that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_element_of_finite
    {α : Type} [PartialOrder α] [Finite α]
    (S : Set α) (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b ≤ a := by sorry
