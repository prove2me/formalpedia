-- Prove2me | Theorems.Thm_exists_max_nat_on_finite_predicate__p2m_c1b261ba_306d_4a6e_a5c0_9da269f5f325_a1
-- name    : exists_max_nat_on_finite_predicate__p2m_c1b261ba_306d_4a6e_a5c0_9da269f5f325_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:53:35.968163+00:00
-- url     : https://prove2.me/theorems/59768c7d-57bb-4ab1-962c-1d86baa4e42c
-- title:
--   Maximum of a natural-valued function on a finite nonempty predicate
-- statement:
--   For a finite type, any nonempty predicate-selected subset contains an element maximizing a natural-valued function.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_max_nat_on_finite_predicate__p2m_c1b261ba_306d_4a6e_a5c0_9da269f5f325_a1
    {α : Type} [Fintype α] (P : α → Prop) (hP : ∃ a, P a) (f : α → Nat) :
    ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by sorry
