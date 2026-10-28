-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_mem_of_bounded_nat_set
-- name    : WilliamsonShmoys.exists_maximal_mem_of_bounded_nat_set
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:54:38.795398+00:00
-- url     : https://prove2.me/theorems/9a34328e-a4e1-4d3a-b876-e1b2cc37bd8d
-- title:
--   Maximum of a nonempty bounded set of natural numbers
-- statement:
--   Every nonempty set of natural numbers bounded above contains a member at least as large as every other member.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_mem_of_bounded_nat_set
    (S : Set Nat) (B : Nat) (hS : S.Nonempty)
    (hB : ∀ n ∈ S, n ≤ B) :
    ∃ m ∈ S, ∀ n ∈ S, n ≤ m := by sorry
