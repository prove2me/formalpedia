-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_member_of_finite_set
-- name    : WilliamsonShmoys.exists_maximal_member_of_finite_set
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:51:58.866655+00:00
-- url     : https://prove2.me/theorems/3826b634-9d3d-4e94-9fc2-3f414f2a76c7
-- title:
--   A nonempty subset of a finite partial order has a maximal member
-- statement:
--   Every nonempty subset of a finite partially ordered type contains a member with no strictly greater member in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_member_of_finite_set
    {α : Type} [Fintype α] [PartialOrder α]
    (S : Set α) (hS : S.Nonempty) :
    ∃ a, a ∈ S ∧ ∀ b, b ∈ S → a ≤ b → b ≤ a := by sorry
