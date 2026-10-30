-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_card_of_predicate__p2m_8f4450fd_25bb_4306_b9c5_7a9c9b261a7b_a2
-- name    : WilliamsonShmoys.exists_max_card_of_predicate__p2m_8f4450fd_25bb_4306_b9c5_7a9c9b261a7b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:29:39.074347+00:00
-- url     : https://prove2.me/theorems/716e3e8d-2e12-43d1-84e7-baad2177e873
-- title:
--   A predicate on a finite type has a maximum value
-- statement:
--   For a nonempty predicate on a finite type, a natural-valued function attains a maximum among elements satisfying the predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_card_of_predicate__p2m_8f4450fd_25bb_4306_b9c5_7a9c9b261a7b_a2 {α : Type} [Fintype α] (P : α → Prop) (f : α → Nat) (hex : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by sorry
