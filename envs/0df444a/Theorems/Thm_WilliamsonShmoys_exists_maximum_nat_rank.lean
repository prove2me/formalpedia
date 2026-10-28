-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximum_nat_rank
-- name    : WilliamsonShmoys.exists_maximum_nat_rank
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:36:13.918462+00:00
-- url     : https://prove2.me/theorems/3b44da3a-bdd3-477b-814a-a3237a7daad3
-- title:
--   Maximum of a bounded natural-valued family
-- statement:
--   Every nonempty family with a natural-valued rank bounded by N contains a member of maximum rank. This replaces the search among graph extensions with a finite search among the attainable ranks in 0 through N. A proof can filter that finite interval by attainability, take its maximum, and choose a witness attaining it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximum_nat_rank
    {α : Type} (S : α → Prop) (r : α → Nat) (N : Nat)
    (hne : ∃ a, S a)
    (hbound : ∀ a, S a → r a ≤ N) :
    ∃ a, S a ∧ ∀ b, S b → r b ≤ r a := by sorry
