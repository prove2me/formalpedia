-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_exists_maximal_of_nonempty__p2m_7f3e1c59_fb8d_479f_ad2c_408c88d9882e_a1
-- name    : WilliamsonShmoys.finite_exists_maximal_of_nonempty__p2m_7f3e1c59_fb8d_479f_ad2c_408c88d9882e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:01:23.155529+00:00
-- url     : https://prove2.me/theorems/4375844d-a202-4a9b-8e89-8b4bdd760ddc
-- title:
--   Finite partial orders have maximal elements in every nonempty subset
-- statement:
--   In a finite partial order, every nonempty subset contains an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_exists_maximal_of_nonempty__p2m_7f3e1c59_fb8d_479f_ad2c_408c88d9882e_a1
    {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop)
    (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by sorry
