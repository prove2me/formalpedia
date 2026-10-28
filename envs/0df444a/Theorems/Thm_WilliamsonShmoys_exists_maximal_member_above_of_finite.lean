-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_member_above_of_finite
-- name    : WilliamsonShmoys.exists_maximal_member_above_of_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:20:34.455566+00:00
-- url     : https://prove2.me/theorems/84a8fceb-e7c7-406c-9f5d-9ba1b7dccc88
-- title:
--   Maximal element above a given element in a finite partial order
-- statement:
--   In a finite partial order, if a predicate is inherited by smaller elements and holds at a, there is a maximal element satisfying it above a.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_member_above_of_finite
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop)
    (hdown : ∀ {a b : α}, a ≤ b → P b → P a)
    (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧
      ∀ c : α, b ≤ c → P c → c = b := by sorry
