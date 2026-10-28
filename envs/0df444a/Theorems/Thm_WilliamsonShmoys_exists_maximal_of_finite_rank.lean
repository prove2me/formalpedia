-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_of_finite_rank
-- name    : WilliamsonShmoys.exists_maximal_of_finite_rank
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:24:43.420075+00:00
-- url     : https://prove2.me/theorems/15952c33-f71b-46a8-9be0-b2e0ced02c8a
-- title:
--   Maximal element from a finite strict rank
-- statement:
--   For a finite type, if every one-way related pair strictly increases a natural-valued rank, every nonempty predicate has an element with no strictly larger related element in that predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_of_finite_rank {α : Type} [Fintype α] (r : α → α → Prop) (P : α → Prop) (rank : α → Nat) (hstrict : ∀ a b, r a b → ¬ r b a → rank a < rank b) (hne : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → r a b → r b a := by sorry
