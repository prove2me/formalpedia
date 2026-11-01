-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_nat_on_finite_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1
-- name    : WilliamsonShmoys.exists_max_nat_on_finite_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:25:33.759381+00:00
-- url     : https://prove2.me/theorems/0e8f0ade-09a7-44d7-9270-33c9353cded6
-- title:
--   A natural-valued function attains a maximum on a nonempty predicate over a finite type
-- statement:
--   On a finite type, any natural-valued function has a maximum among the elements satisfying a nonempty predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_nat_on_finite_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1 {α : Type} [Finite α] (P : α → Prop) (f : α → Nat) (hex : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by sorry
